from pathlib import Path
from fractions import Fraction as F
import json,hashlib,sqlite3,itertools as I,time,collections
p=Path(__file__).parent;b=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3');src=b/'residual-ten-D5-five-311-low-edge-allocation';read=lambda f:json.loads(f.read_text());hashes={}
for mf in ['pins.json','input-pins.json']:
 for n,h in read(src/mf).items():
  f=src/n;assert hashlib.sha256(f.read_bytes()).hexdigest()==h;hashes[str(f)]=h
con=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);con.row_factory=sqlite3.Row
states=[dict(con.execute('select id,status,resolution from review_requests where id=?',(i,)).fetchone()) for i in [2467,2469,2473,2476,2478]];assert all(s['status']=='resolved' and s['resolution'].startswith('PASS') for s in states)
prop=read(b/'residual-ten-D5-five-311-low-propagation/results.json')['records'];capacity={r['root']:r for r in read(b/'residual-ten-D5-five-311-low-edge-capacity/results.json')['records']};joint={r['root']:r for r in read(b/'residual-ten-D5-five-311-nonempty-joint/results.json')['records']};graphs={r['root']:r for r in read(b/'residual-ten-D5-five-311-high-matchings/results.json')['records']};pack=read(b/'residual-ten-D5-five-311-packing/results.json')['records'];dom=read(b/'residual-ten-D5-supports/results.json')['records'];ctx=read(Path('/tmp/erdos85-sol1-review2473/contexts.json'))
models=read(src/'models.json');results=read(src/'results.json');index=read(src/'case-index.json');assert models['status']=='COMPLETE' and results['status']=='INCOMPLETE';expected=[(r['root'],a) for r in prop for a in r['survivors']];assert len(expected)==len(models['records'])==len(results['records'])==len(index)==94
outcomes={r['root']:r for r in results['records']};assert set(outcomes)==set(range(94));start=time.monotonic();out=[];status='INCOMPLETE'
def flip(m):return sum(1<<(e^1) for e in range(10) if m&(1<<e))
try:
 for mid,(rid,a) in enumerate(expected):
  if time.monotonic()-start>30:raise TimeoutError
  model=models['records'][mid];ans=outcomes[mid];source=joint[rid];ai=a['assignment'];ci=source['class'];assert (model['root'],model['source_root'],model['assignment'],model['class'])==(mid,rid,ai,ci);assert index[mid]=={'root':mid,'source_root':rid,'source_assignment':ai,'class':ci};assert ans['source_root']==rid and ans['class']==ci
  lows=next(x['lows'] for x in capacity[rid]['survivors'] if x['assignment']==ai);q=source['survivors'][ai];root=pack[ci]['survivors'][source['source_root']];primary=[dom[ci]['high3'][j] for j in root['high3']];S=[set(t) for s in primary for t in (s,[e^1 for e in s])];R=[set() for _ in range(10)]
  for v,w in dom[ci]['edges']:R[v].add(w);R[w].add(v)
  N=[set() for _ in range(70)]
  def edge(u,v):N[u].add(v);N[v].add(u)
  for v in range(10):
   for w in R[v]:edge(v,w)
  for v,s in enumerate(S):
   for r in s:edge(10+v,r)
  for v,w in graphs[source['packing_root']]['survivors'][source['graph']]['edges']:edge(10+v,10+w)
  for i,(v,r) in enumerate(lows):
   edge(20+i,r)
   if v>=0:edge(20+i,10+v)
  for i,j in a['forced_edges']:edge(20+i,20+j)
  edges=list(map(tuple,a['remaining_edges']));n=len(edges);assert [x['edge'] for x in model['variables']]==a['remaining_edges'] and model['bounds']==[[0,1]]*n
  incident=[[] for _ in lows]
  for k,(i,j) in enumerate(edges):incident[i].append((k,j));incident[j].append((k,i))
  constraints={}
  def add(label,row,lo,hi):constraints[label]=({k:v for k,v in row.items() if v},lo,hi)
  C=[[0]*10 for _ in range(10)];B=[[collections.Counter() for _ in range(10)] for _ in range(10)]
  for i,(v,r) in enumerate(lows):
   fixed=[j-20 for j in N[20+i] if j>=20];goal=6 if v>=0 else 7;add('degree '+str(i),dict.fromkeys([k for k,j in incident[i]],1),goal-len(fixed),goal-len(fixed))
   allowed=set(range(10))-R[r]-(S[v] if v>=0 else set())
   for e in range(10):
    f=sum(lows[j][1]==e for j in fixed);lo=int(e in allowed)-f if v>=0 else -f;hi=int(e in allowed)-f
    add('support '+str((i,e)),{k:1 for k,j in incident[i] if lows[j][1]==e},lo,hi)
    if v<0:
     C[r][e]+=int(e not in R[r])-f
     for k,j in incident[i]:
      if lows[j][1]==e:B[r][e][k]-=1
  for e in range(10):
   row=collections.Counter()
   for r in range(10):
    for k,v in B[r][e].items():row[k]+=v
   rhs=q['remaining_columns'][e]-sum(C[r][e] for r in range(10));add('defect column '+str(e),row,rhs,rhs)
  context=next(c for c in ctx[str(rid)] if c['rows']==q['rows']);T=context['T']
  for i,j in I.combinations(range(10),2):
   row=collections.Counter(B[j][i])
   for k,v in B[i][j].items():row[k]-=v
   rhs=T[i][j]-C[j][i]+C[i][j];add('comm '+str((i,j)),row,rhs,rhs)
  adjacency=[set(j-20 for j in N[20+i] if j>=20) for i in range(50)];common=[[bool(N[20+i]&N[20+j]) for j in range(50)] for i in range(50)];conflicts=0
  for k,(i,j) in enumerate(edges):
   for h in range(k+1,n):
    v,w=edges[h];ends=[i,j,v,w];odd=[x for x in set(ends) if ends.count(x)==1]
    bad=common[odd[0]][odd[1]] if len(odd)==2 else ((v in adjacency[i] and w in adjacency[j]) or (w in adjacency[i] and v in adjacency[j]))
    if bad:add('C4 pair '+str((k,h)),{k:1,h:1},0,1);conflicts+=1
  assert conflicts==model['conflicts'];assert len(model['constraints'])==len(constraints) and {c['label'] for c in model['constraints']}==set(constraints)
  inequalities={}
  for j,c in enumerate(model['constraints']):
   row,lo,hi=constraints[c['label']];assert len(c['coefficients'])==len(row) and dict(c['coefficients'])==row and c['lower']==lo and c['upper']==hi
   inequalities['constraint',j,'upper']=(row,hi);inequalities['constraint',j,'lower']=({k:-v for k,v in row.items()},-lo)
  for k in range(n):inequalities['bound',k,'upper']=({k:1},1);inequalities['bound',k,'lower']=({k:-1},0)
  if ans['status']=='EXACT_RATIONAL_WITNESS':
   x=list(map(F,ans['assignment']));assert len(x)==n and all(sum((x[k]*v for k,v in row.items()),F(0))<=rhs for row,rhs in inequalities.values());assert any(v.denominator!=1 for v in x)
  elif ans['status']=='EXACT_FARKAS_CONTRADICTION':
   total=collections.defaultdict(F);rhs=F(0)
   for t in ans['terms']:
    w=F(t['weight']);assert w>=0;row,z=inequalities[tuple(t['label'])];rhs+=w*z
    for k,v in row.items():total[k]+=w*v
   assert all(v==0 for v in total.values()) and rhs<0 and rhs==F(ans['rhs'])
  else:assert mid==46 and ans['status']=='UNKNOWN'
  out.append({'root':mid,'source_root':rid,'source_assignment':ai,'status':ans['status'],'variables':n,'conflicts':conflicts})
 status='COMPLETE'
except TimeoutError:pass
result={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'hashes':hashes,'premises':states,'records':out};(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':status,'seconds':result['seconds'],'hashes':len(hashes),'models':len(out),'conflicts':sum(x['conflicts'] for x in out),'outcomes':dict(collections.Counter(x['status'] for x in out))}))
