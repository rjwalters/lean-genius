from pathlib import Path
import json,itertools as it,time
p=Path(__file__).resolve().parent;b=p.parent;start=time.monotonic();prop=json.loads((b/'residual-ten-D5-five-311-low-propagation/results.json').read_text())['records'];edgecases={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-low-edge-capacity/results.json').read_text())['records']};joint={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-nonempty-joint/results.json').read_text())['records']};graphs={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-high-matchings/results.json').read_text())['records']};pack=json.loads((b/'residual-ten-D5-five-311-packing/results.json').read_text())['records'];dom=json.loads((b/'residual-ten-D5-supports/results.json').read_text())['records'];out=[]
def flip(m):return sum(1<<(i^1) for i in range(10) if m>>i&1)
def guard():
 if time.monotonic()-start>=30:raise TimeoutError
for entry in prop:
 source=joint[entry['root']];ci=source['class'];root=pack[ci]['survivors'][source['source_root']];c=dom[ci];ss=[c['high3'][j] for j in root['high3']];S=[set(t) for s in ss for t in (s,[e^1 for e in s])];rho={v:w for a,z in c['edges'] for v,w in [(a,z),(z,a)]};Hg=graphs[source['packing_root']]['survivors'][source['graph']]['edges'];lookup={r['assignment']:r for r in edgecases[entry['root']]['survivors']}
 for a in entry['survivors']:
  guard();ai=a['assignment'];lows=lookup[ai]['lows'];qrow=source['survivors'][ai];Q=[x for m in qrow['rows'] for x in (m,flip(m))];N=[set() for _ in range(70)];fixed=[set() for _ in lows];edges=a['remaining_edges'];n=len(edges);constraints=[]
  def edge(v,w):N[v].add(w);N[w].add(v)
  for v,w in c['edges']:edge(v,w)
  for v,s in enumerate(S):
   for r in s:edge(10+v,r)
  for v,w in Hg:edge(10+v,10+w)
  for i,(v,r) in enumerate(lows):
   edge(20+i,r)
   if v>=0:edge(20+i,10+v)
  for i,j in a['forced_edges']:edge(20+i,20+j);fixed[i].add(j);fixed[j].add(i)
  incident=[{} for _ in lows]
  for k,(i,j) in enumerate(edges):incident[i][k]=j;incident[j][k]=i
  def add(label,coeff,lo,hi):constraints.append({'label':label,'coefficients':sorted((i,v) for i,v in coeff.items() if v),'lower':lo,'upper':hi})
  for i,(v,r) in enumerate(lows):
   goal=6 if v>=0 else 7;add('degree '+str(i),{k:1 for k in incident[i]},goal-len(fixed[i]),goal-len(fixed[i]));targets=set(range(10))-({rho[r]}|(S[v] if v>=0 else set()))
   for e in range(10):
    selected=sum(lows[j][1]==e for j in fixed[i]);upper=int(e in targets)-selected;lower=upper if v>=0 else -selected
    add('support '+str((i,e)),{k:1 for k,j in incident[i].items() if lows[j][1]==e},lower,upper)
  const=[[qrow['inactive'][r]*int(e!=rho[r]) for e in range(10)] for r in range(10)];coeff=[[{} for _ in range(10)] for _ in range(10)]
  for i,(v,r) in enumerate(lows):
   if v>=0:continue
   for j in fixed[i]:const[r][lows[j][1]]-=1
   for k,j in incident[i].items():
    e=lows[j][1];coeff[r][e][k]=coeff[r][e].get(k,0)-1
  for e in range(10):
   co={}
   for r in range(10):
    for k,v in coeff[r][e].items():co[k]=co.get(k,0)+v
   rhs=qrow['remaining_columns'][e]-sum(const[r][e] for r in range(10));add('defect column '+str(e),co,rhs,rhs)
  Z=[[int(i!=j and not any(i in s and j in s for s in S)) for j in range(10)] for i in range(10)]
  for i,j in it.combinations(range(10),2):
   T=Z[rho[i]][j]-Z[i][rho[j]]-sum(((m>>i)&1)*(j in s)-(i in s)*((m>>j)&1) for m,s in zip(Q,S));co={}
   for k,v in coeff[j][i].items():co[k]=co.get(k,0)+v
   for k,v in coeff[i][j].items():co[k]=co.get(k,0)-v
   rhs=T-const[j][i]+const[i][j];add('comm '+str((i,j)),co,rhs,rhs)
  masks=[sum(1<<v for v in ns) for ns in N];conflicts=0
  for k,(i,j) in enumerate(edges):
   for h in range(k+1,n):
    v,w=edges[h];common=set((i,j))&set((v,w));bad=False
    if common:
     x=next(iter(common));y=next(z for z in (i,j) if z!=x);z=next(z for z in (v,w) if z!=x);bad=bool(masks[20+y]&masks[20+z])
    else:bad=(20+v in N[20+i] and 20+w in N[20+j]) or (20+w in N[20+i] and 20+v in N[20+j])
    if bad:add('C4 pair '+str((k,h)),{k:1,h:1},0,1);conflicts+=1
  out.append({'root':len(out),'source_root':entry['root'],'assignment':ai,'class':ci,'variables':[{'edge':e} for e in edges],'bounds':[[0,1] for e in edges],'constraints':constraints,'conflicts':conflicts})
r={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'models.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'seconds':r['seconds'],'models':len(out),'max_variables':max(len(r['variables']) for r in out),'conflicts':sum(r['conflicts'] for r in out)}))
