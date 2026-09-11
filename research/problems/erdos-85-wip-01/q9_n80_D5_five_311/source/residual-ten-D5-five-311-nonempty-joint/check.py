from pathlib import Path
import json,itertools as it,time,math,numpy as np
p=Path(__file__).resolve().parent;b=p.parent;start=time.monotonic();alloc=json.loads((b/'residual-ten-D5-five-311-fixed-allocation/results.json').read_text())['records'];graphs={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-high-matchings/results.json').read_text())['records']};pack=json.loads((b/'residual-ten-D5-five-311-packing/results.json').read_text())['records'];dom=json.loads((b/'residual-ten-D5-supports/results.json').read_text())['records'];out=[];pairs=list(it.combinations(range(10),2))
def flip(m):return sum(1<<(i^1) for i in range(10) if m>>i&1)
def guard():
 if time.monotonic()-start>=30:raise TimeoutError
try:
 for source in alloc:
  if source['status']!='EXACT_RATIONAL_WITNESS':continue
  graph=graphs[source['packing_root']]['survivors'][source['graph']]
  if not graph['edges']:continue
  guard();ci=source['class'];root=pack[ci]['survivors'][source['source_root']];c=dom[ci];R=[set() for _ in range(10)];H=[set() for _ in range(10)]
  for a,z in c['edges']:R[a].add(z);R[z].add(a)
  for a,z in graph['edges']:H[a].add(z);H[z].add(a)
  ss=[c['high3'][j] for j in root['high3']];S=[set(t) for s in ss for t in (s,[e^1 for e in s])];covered=[set().union(*(R[e] for e in s),*(S[w] for w in H[v])) for v,s in enumerate(S)];low=np.array([8-sum(e in s for s in S) for e in range(10)],dtype=np.int16);a=np.array([sum(e not in C for C in covered) for e in range(10)],dtype=np.int16);diagbase=low-np.array([sum(e not in C and e in s for C,s in zip(covered,S)) for e in range(10)],dtype=np.int16)
  Z=[[int(i!=j and not R[i]&R[j] and not any(i in s and j in s for s in S)) for j in range(10)] for i in range(10)];D=np.array([sum(Z[k][j] for k in R[i])-sum(Z[i][k] for k in R[j]) for i,j in pairs],dtype=np.int16);domains=[]
  for v in range(0,10,2):
   ds=[]
   for m in graph['Q_domains'][v]:
    other=flip(m)
    if other not in graph['Q_domains'][v+1]:continue
    qs=[m,other];col=[sum((x>>e)&1 for x in qs) for e in range(10)];comm=[sum(((x>>i)&1)*(j in s)-(i in s)*((x>>j)&1) for x,s in zip(qs,S[v:v+2])) for i,j in pairs];diag=[sum(((x>>e)&1)*(e in s) for x,s in zip(qs,S[v:v+2])) for e in range(10)];ds.append((m,col+comm+diag))
   domains.append(ds)
  ix=np.array(list(it.product(*(range(len(ds)) for ds in domains))),dtype=np.int16);X=np.zeros((len(ix),65),dtype=np.int16)
  for j,ds in enumerate(domains):X+=np.array([x[1] for x in ds],dtype=np.int16)[ix[:,j]]
  q=np.array(root['q'],dtype=np.int16);left=q-X[:,:10];u=low-a+X[:,:10];keep=np.all(left>=0,axis=1)&np.all(u>=0,axis=1);ix=ix[keep];X=X[keep];left=left[keep];u=u[keep];ncol=len(ix)
  T=np.zeros((len(ix),10,10),dtype=np.int16)
  for j,(v,w) in enumerate(pairs):T[:,v,w]=D[j]-X[:,10+j];T[:,w,v]=-T[:,v,w]
  required=left-T.sum(axis=2);minimum=np.maximum(T,0).sum(axis=2);cap=np.max(np.maximum(-T,0),axis=2);keep=np.all(required==2*u,axis=1)&np.all(minimum<=left,axis=1)&np.all(cap<=u,axis=1)
  for v in range(10):
   for w in R[v]:keep&=T[:,v,w]==0
  ix=ix[keep];X=X[keep];left=left[keep];u=u[keep];T=T[keep];minimum=minimum[keep];nflow=len(ix);parity=(diagbase+X[:,55:])%2;rema=left-minimum;keep=np.all(parity<=np.minimum(rema,u),axis=1);ids=np.nonzero(keep)[0];survivors=[]
  for z in ids:
   survivors.append({'rows':[domains[j][i][0] for j,i in enumerate(ix[z])],'inactive':u[z].tolist(),'remaining_columns':left[z].tolist(),'diagonal_parity':parity[z].tolist()})
  out.append({'root':source['root'],'packing_root':source['packing_root'],'class':ci,'source_root':source['source_root'],'graph':source['graph'],'status':'COMPLETE','products':math.prod(map(len,domains)),'column_capacity':ncol,'flow':nflow,'survivors':survivors})
 status='COMPLETE'
except TimeoutError:status='INCOMPLETE'
seen={r['root'] for r in out}
for source in alloc:
 if source['status']=='EXACT_RATIONAL_WITNESS' and graphs[source['packing_root']]['survivors'][source['graph']]['edges'] and source['root'] not in seen:out.append({'root':source['root'],'status':'UNVISITED'})
r={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':status,'seconds':r['seconds'],'complete':sum(r['status']=='COMPLETE' for r in out),'products':sum(r.get('products',0) for r in out),'flow':sum(r.get('flow',0) for r in out),'positive_cases':sum(bool(r.get('survivors')) for r in out),'assignments':sum(len(r.get('survivors',[])) for r in out)}))
