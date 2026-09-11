import json,hashlib,itertools,time
from pathlib import Path
start=time.monotonic(); src=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-order3-color-lp-cover'); out=Path(__file__).parent
pins=json.loads((src/'pins.json').read_text())
for n,h in pins.items(): assert hashlib.sha256((src/n).read_bytes()).hexdigest()==h
ip=json.loads((src/'input-pin.json').read_text()); assert hashlib.sha256(Path(ip['path']).read_bytes()).hexdigest()==ip['sha256']
expected={r['representative_code']:r['orbit_size'] for r in map(json.loads,Path(ip['path']).read_text().splitlines())}
perms=list(itertools.permutations(range(3))); edges=list(itertools.combinations(range(5),2)); words=list(itertools.product(range(3),repeat=5))
def mat(p):return [[int(p[a]==b) for b in range(3)] for a in range(3)]
def mm(a,b):return [[sum(a[i][k]*b[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
E=[[0,0,0],[0,0,1],[0,1,0]];seen=set();counts={};covered={}
for r in map(json.loads,(src/'receipts.jsonl').read_text().splitlines()):
 code=r['code'];assert code not in seen and expected[code]==r['orbit_size'];seen.add(code)
 digits=[];z=code
 for i in range(10):digits.append(z%6);z//=6
 assert z==0
 P={}
 for (u,v),d in zip(edges,reversed(digits)):
  P[u,v]=mat(perms[d]);P[v,u]=[list(x) for x in zip(*P[u,v])]
 caps={}
 for u,v in edges:
  terms=[mm(E,P[u,v]),mm(P[u,v],E)]+[mm(P[u,t],P[t,v]) for t in range(5) if t!=u and t!=v]
  caps[u,v]=[[3-sum(m[a][b] for m in terms) for b in range(3)] for a in range(3)]
 ids=[i for i,w in enumerate(words) if all(caps[u,v][w[u]][w[v]]>=1 for u,v in edges)]
 assert len(ids)==r['supported_words']
 # Build sparse row supports without importing author code.
 rows=[];rhs=[]
 for u in range(5):
  for a in range(3):
   for sign in [-1,1]: rows.append({i:sign for i in ids if words[i][u]==a});rhs.append(sign*(4 if a==0 else 3))
 for u,v in edges:
  for a in range(3):
   for b in range(3):rows.append({i:1 for i in ids if words[i][u]==a and words[i][v]==b});rhs.append(caps[u,v][a][b])
 status=r['status'];counts[status]=counts.get(status,0)+1;covered[status]=covered.get(status,0)+r['orbit_size']
 if status=='EXACT_INFEASIBLE':
  c=r['certificate'];assert len(c)==len(dict(c)); coeff=dict.fromkeys(ids,0); dot=0
  for j,v in c:
   assert type(j)==int and 0<=j<120 and type(v)==int and v>0
   dot+=v*rhs[j]
   for i,a in rows[j].items():coeff[i]+=v*a
  assert dot<0 and min(coeff.values(),default=0)>=0
 elif status=='EXACT_FRACTIONAL_FEASIBLE':
  den=r['denominator'];assert type(den)==int and den>0; w=dict(r['witness']);assert len(w)==len(r['witness'])
  assert all(i in ids and type(v)==int and v>0 for i,v in w.items())
  for row,b in zip(rows,rhs):assert sum(row.get(i,0)*v for i,v in w.items())<=den*b
 else:raise ValueError(status)
assert seen==set(expected) and len(seen)==1284
result=dict(status='PASS',cases=len(seen),counts=counts,labelled_coverage=covered,seconds=time.monotonic()-start,method='independent 3x3 matrix reconstruction and exact sparse integer verification')
(out/'results.json').write_text(json.dumps(result,indent=2)+'\n');(out/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n'); print(json.dumps(result))
