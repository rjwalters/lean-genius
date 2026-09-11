from pathlib import Path
from itertools import permutations,combinations,product
import json,hashlib,time
s=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-order3-integer-color-cover');d=Path(__file__).resolve().parent;t=time.monotonic()
for f,h in json.loads((s/'pins.json').read_text()).items():assert hashlib.sha256((s/f).read_bytes()).hexdigest()==h
source=s.parent/'q9-order3-color-lp-cover/receipts.jsonl'
assert hashlib.sha256(source.read_bytes()).hexdigest()==json.loads((s/'launch.json').read_text())['input_source_sha256']
expected={r['code'] for r in map(json.loads,source.read_text().splitlines()) if r['status']=='EXACT_FRACTIONAL_FEASIBLE'}
rs=list(map(json.loads,(s/'receipts.jsonl').read_text().splitlines()));assert len(rs)==len(expected)==576 and {r['code'] for r in rs}==expected
ps=list(permutations(range(3)));pairs=list(combinations(range(5),2));words=list(product(range(3),repeat=5));E=[[0,0,0],[0,0,1],[0,1,0]]
def mul(A,B):return [[sum(A[a][t]*B[t][b] for t in range(3)) for b in range(3)] for a in range(3)]
lines=(s/'input.txt').read_text().splitlines();assert int(lines[0])==576 and len(lines)==577
neg=[];pos=0
for line,r in zip(lines[1:],rs):
 data=list(map(int,line.split()));code,n=data[:2];assert code==r['code'];ds=[];z=code
 for i in range(10):ds.append(z%6);z//=6
 assert z==0;ds.reverse();M={}
 for (u,v),k in zip(pairs,ds):
  M[u,v]=[[int(ps[k][a]==b) for b in range(3)] for a in range(3)];M[v,u]=list(map(list,zip(*M[u,v])))
 caps={}
 for u,v in pairs:
  parts=[mul(E,M[u,v]),mul(M[u,v],E)]+[mul(M[u,t],M[t,v]) for t in range(5) if t not in (u,v)]
  caps[u,v]=[[3-sum(A[a][b] for A in parts) for b in range(3)] for a in range(3)]
 ids=[]
 for i,w in enumerate(words):
  if any(caps[u,v][w[u]][w[v]]<=0 for u,v in pairs):continue
  if any(E[w[u]][a]+sum(M[v,u][w[v]][a] for v in range(5) if v!=u)>3 for u in range(5) for a in range(3)):continue
  ids.append(i)
 assert ids==data[2:2+n]
 assert data[2+n:]==[caps[u,v][a][b] for u,v in pairs for a in range(3) for b in range(3)]
 if r['status']=='INTEGER_COLORING':
  chosen=r['words'];assert len(chosen)==len(set(chosen))==10 and set(chosen)<=set(ids);ws=[words[i] for i in chosen]
  assert all(sum(w[u]==a for w in ws)==(4,3,3)[a] for u in range(5) for a in range(3))
  assert all(sum(a==b for a,b in zip(x,y))<=3 for x,y in combinations(ws,2))
  assert all(sum((w[u],w[v])==(a,b) for w in ws)<=caps[u,v][a][b] for u,v in pairs for a in range(3) for b in range(3));pos+=1
 else:
  assert r['status']=='COMPLETE_NEGATIVE' and not r['words'];neg.append(line)
assert pos==518 and len(neg)==58
(d/'negative-input.txt').write_text(str(len(neg))+'\n'+'\n'.join(neg)+'\n')
out={'result':'PASS_INPUTS_AND_POSITIVES','cases':576,'positive_witnesses':pos,'negatives_pending':58,'seconds':time.monotonic()-t};(d/'inputs.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
