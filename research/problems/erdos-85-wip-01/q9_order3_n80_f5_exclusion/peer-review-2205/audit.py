from pathlib import Path
from itertools import permutations,combinations,product
import json,hashlib,time,importlib.util
s=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-order3-fractional-residual');d=Path(__file__).resolve().parent;t0=time.monotonic()
for f,h in json.loads((s/'pins.json').read_text()).items():assert hashlib.sha256((s/f).read_bytes()).hexdigest()==h
spec=importlib.util.spec_from_file_location('producer_model',s/'model.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
ps=list(permutations(range(3)));pairs=list(combinations(range(5),2));E=[[0,0,0],[0,0,1],[0,1,0]]
def mul(A,B):return [[sum(A[a][t]*B[t][b] for t in range(3)) for b in range(3)] for a in range(3)]
def independent(code):
 digits=[];z=code
 for i in range(10):digits.append(z%6);z//=6
 assert z==0;digits.reverse();M={}
 for (u,v),k in zip(pairs,digits):
  M[u,v]=[[int(ps[k][a]==b) for b in range(3)] for a in range(3)];M[v,u]=list(map(list,zip(*M[u,v])))
 U={}
 for u,v in pairs:
  summands=[mul(E,M[u,v]),mul(M[u,v],E)]+[mul(M[u,t],M[t,v]) for t in range(5) if t not in (u,v)]
  U[u,v]=[[3-sum(A[a][b] for A in summands) for b in range(3)] for a in range(3)]
 words=[];bounds=[]
 for w in product(range(3),repeat=5):
  b=[[3-E[w[u]][a]-sum(M[v,u][w[v]][a] for v in range(5) if v!=u) for a in range(3)] for u in range(5)]
  if any(x<0 for row in b for x in row) or any(U[u,v][w[u]][w[v]]<=0 for u,v in pairs):continue
  words.append(w);bounds.append(b)
 n=len(words);edges=[]
 for i,w in enumerate(words):
  for j in range(i,n):
   z=words[j]
   if i==j:
    allowed=min(bounds[i][u][w[u]] for u in range(5))>=2
   else:
    allowed=sum(a==b for a,b in zip(w,z))<=3 and all(bounds[i][u][z[u]]>=1 and bounds[j][u][w[u]]>=1 for u in range(5))
   if allowed:edges.append((i,j))
 rows=[];rhs=[];labels=[]
 def add(row,b,label):rows.append({k:v for k,v in row.items() if v});rhs.append(b);labels.append(label)
 for u in range(5):
  for a in range(3):
   for sign in (-1,1):add({i:sign for i,w in enumerate(words) if w[u]==a},sign*(4,3,3)[a],['margin',u,a,sign])
 for u,v in pairs:
  for a in range(3):
   for b in range(3):add({i:1 for i,w in enumerate(words) if (w[u],w[v])==(a,b)},U[u,v][a][b],['pair',u,v,a,b])
 for i,w in enumerate(words):
  add({i:1},1,['selected_bound',i]);inc={}
  for k,(a,b) in enumerate(edges):
   if a==i:inc[n+k]=b
   elif b==i:inc[n+k]=a
  for sign in (-1,1):
   row={i:-4*sign};row.update({k:sign for k in inc});add(row,0,['degree',i,sign])
  for u in range(5):
   for a in range(3):
    row={i:-bounds[i][u][a]};row.update({k:1 for k,j in inc.items() if words[j][u]==a});add(row,0,['neighbor_margin',i,u,a])
  for k in inc:add({i:-2,k:1},0,['edge_bound',i,k])
 return {'code':code,'words':words,'edges':edges,'A':rows,'rhs':rhs,'labels':labels,'variables':n+len(edges)}
batch=list(map(json.loads,(s/'batch.jsonl').read_text().splitlines()));repair=list(map(json.loads,(s/'repaired.jsonl').read_text().splitlines()))
expected=set(json.loads((d.parent/'review-2204/unknown-not-replayed.json').read_text()));assert len(expected)==60
assert len(batch)==59 and {r['code'] for r in batch}==expected-{669268}
certs=[r for r in batch if r['status']=='EXACT_INFEASIBLE']+[r for r in repair if r['status']=='EXACT_REPAIRED_INFEASIBLE']
assert len(certs)==58 and len({r['code'] for r in certs})==58 and {r['code'] for r in certs}==expected-{669268,24538199}
results=[]
for r in certs:
 m=independent(r['code']);assert m==mod.model(r['code']),r['code']
 coeff=[0]*m['variables'];right=0;seen=set()
 for i,weight in r['certificate']:
  assert isinstance(weight,int) and weight>0 and isinstance(i,int) and i not in seen and 0<=i<len(m['A']);seen.add(i)
  right+=weight*m['rhs'][i]
  for j,v in m['A'][i].items():coeff[j]+=weight*v
 assert min(coeff)>=0 and right<0
 results.append({'code':r['code'],'words':len(m['words']),'variables':m['variables'],'constraints':len(m['A']),'terms':len(seen),'min_coefficient':min(coeff),'rhs':right})
(d/'certificates.json').write_text(json.dumps(results,indent=2)+'\n')
out={'status':'PASS','independent_models_and_certificates':58,'unresolved_preserved':[669268,24538199],'seconds':time.monotonic()-t0,'solver_calls':0};(d/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
