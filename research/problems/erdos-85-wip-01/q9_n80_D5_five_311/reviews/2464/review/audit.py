from pathlib import Path
from fractions import Fraction as F
import json,hashlib,itertools as I,time,sqlite3,collections
p=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/residual-ten-D5-five-311-allocation');read=lambda f:json.loads(f.read_text());checks={}
for mf in [src/'pins.json',src/'input-pins.json']:
 for name,h in read(mf).items():
  f=mf.parent/name;assert hashlib.sha256(f.read_bytes()).hexdigest()==h;checks[str(f)]=h
con=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);con.row_factory=sqlite3.Row
states=[dict(con.execute('select id,status,resolution from review_requests where id=?',(i,)).fetchone()) for i in [2251,2458,2460,2463]];assert all(r['status']=='resolved' and r['resolution'].startswith('PASS') for r in states)
classes=read(src.parent/'residual-ten-D5-supports/results.json')['records'];pack=read(src.parent/'residual-ten-D5-five-311-packing/results.json')['records']
models=read(src/'models.json');outcomes=read(src/'results.json');assert models['status']==outcomes['status']=='COMPLETE'
expected=[(g['class'],ri) for g in pack for ri in range(len(g['survivors']))]
assert len(expected)==len(set(expected))==3856
M={r['root']:r for r in models['records']};O={r['root']:r for r in outcomes['records']};assert set(M)==set(O)==set(range(3856)) and len(M)==len(models['records']) and len(O)==len(outcomes['records'])
start=time.monotonic();records=[];status='INCOMPLETE'
try:
 for mi,(ci,ri) in enumerate(expected):
  if time.monotonic()-start>30:raise TimeoutError
  model=M[mi];answer=O[mi];assert (model['class'],model['source_root'])==(ci,ri) and answer['source_root']==ri
  c=classes[ci];root=pack[ci]['survivors'][ri];R=[set() for _ in range(10)]
  for a,b in c['edges']:R[a].add(b);R[b].add(a)
  primary=[c['high3'][j] for j in root['high3']]
  S=[t for x in primary for t in (set(x),{e^1 for e in x})];N=len(S);assert N==10
  B=[len(s)+2-sum(len(R[e]) for e in s) for s in S];low=[9-len(R[e])-sum(e in s for s in S) for e in range(10)]
  middle=[set().union(*(R[e] for e in s)) for s in S]
  # Direct partial adjacency recovers residual defect pairs independently.
  adj=[set(s) for s in R]+[set(s) for s in S]
  for v,s in enumerate(S):
   for e in s:adj[e].add(10+v)
  Z=[{j for j in range(10) if i!=j and not adj[i]&adj[j]} for i in range(10)]
  q=[6-len(R[e])-len(Z[e]) for e in range(10)];assert q==root['q']
  D={(i,j):len(R[i]&Z[j])-len(Z[i]&R[j]) for i,j in I.combinations(range(10),2)}
  # Check every identified variable orbit; keep producer indices solely as labels.
  required={(kind,frozenset(((v,e),(v^1,e^1)))) for kind,size in [('high',N),('low_aggregate',10)] for v in range(size) for e in range(10)}
  got=[];occ=[];bounds=[]
  for var in model['variables']:
   kind=var['type'];orbit=frozenset(map(tuple,var['orbit']));got.append((kind,orbit));assert len(orbit)==2
   limits=[];os=[]
   for v,e in orbit:
    if kind=='high':
     limits.append((0,int(e not in middle[v] and B[v]>0)));os.append((kind,v,e,S[v]))
    else:
     assert kind=='low_aggregate';limits.append((0,0 if e in R[v] else low[v]));os.append((kind,v,e,{v}))
   assert limits[0]==limits[1];bounds.append(limits[0]);occ.append(os)
  assert len(got)==len(set(got)) and set(got)==required and [list(x) for x in bounds]==model['bounds']
  n=len(occ);expectedconstraints={}
  for e in range(10):expectedconstraints['column '+str(e)]=([sum(t==e for kind,v,t,s in os) for os in occ],q[e],q[e])
  for v in range(N):expectedconstraints['high budget '+str(v)]=([sum(kind=='high' and a==v for kind,a,e,s in os) for os in occ],B[v]%2,B[v])
  for v in range(10):expectedconstraints['low budget '+str(v)]=([sum(kind=='low_aggregate' and a==v for kind,a,e,s in os) for os in occ],((3-len(R[v]))%2)*low[v],(3-len(R[v]))*low[v])
  for (i,j),rhs in D.items():expectedconstraints['comm '+str((i,j))]=([sum(int(e==i and j in s)-int(i in s and e==j) for kind,v,e,s in os) for os in occ],rhs,rhs)
  assert len(model['constraints'])==len(expectedconstraints) and {x['label'] for x in model['constraints']}==set(expectedconstraints)
  inequalities={}
  for j,cst in enumerate(model['constraints']):
   dense,lo,hi=expectedconstraints[cst['label']];sparse={i:a for i,a in enumerate(dense) if a}
   assert dict(cst['coefficients'])==sparse and len(cst['coefficients'])==len(sparse) and cst['lower']==lo and cst['upper']==hi
   inequalities['constraint',j,'upper']=(sparse,hi);inequalities['constraint',j,'lower']=({i:-a for i,a in sparse.items()},-lo)
  for j,(lo,hi) in enumerate(bounds):inequalities['bound',j,'upper']=({j:1},hi);inequalities['bound',j,'lower']=({j:-1},-lo)
  if answer['status']=='EXACT_FARKAS_CONTRADICTION':
   coeff=collections.defaultdict(F);rhs=F(0)
   for term in answer['terms']:
    weight=F(term['weight']);assert weight>=0;row,b=inequalities[tuple(term['label'])];rhs+=weight*b
    for j,a in row.items():coeff[j]+=weight*a
   assert all(x==0 for x in coeff.values()) and rhs<0 and rhs==F(answer['rhs'])
   record={'root':mi,'source_root':ri,'status':'EXACT_FARKAS_CONTRADICTION','rhs':str(rhs),'terms':len(answer['terms'])}
  else:
   assert answer['status']=='EXACT_RATIONAL_WITNESS';x=list(map(F,answer['assignment']));assert len(x)==n
   assert all(sum((x[j]*a for j,a in row.items()),F(0))<=b for row,b in inequalities.values())
   record={'root':mi,'source_root':ri,'status':'EXACT_RATIONAL_WITNESS','integral':all(t.denominator==1 for t in x),'max_denominator':max(t.denominator for t in x)}
  record.update(variables=n,constraints=len(expectedconstraints));records.append(record)
 status='COMPLETE'
except TimeoutError:pass
r={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'hashes':checks,'premises':states,'records':records};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({'status':status,'seconds':r['seconds'],'hashes':len(checks),'models':len(records),'farkas':sum(x['status']=='EXACT_FARKAS_CONTRADICTION' for x in records),'witnesses':sum(x['status']=='EXACT_RATIONAL_WITNESS' for x in records),'integral':sum(x.get('integral',False) for x in records)}))
