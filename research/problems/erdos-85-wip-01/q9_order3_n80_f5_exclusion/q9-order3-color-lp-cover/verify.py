from pathlib import Path
import itertools,json,time
p=Path(__file__).resolve().parent;start=time.monotonic()
words=list(itertools.product(range(3),repeat=5));ps=list(itertools.permutations(range(3)));pairs=list(itertools.combinations(range(5),2))
labels=[('m',u,a,s) for u in range(5) for a in range(3) for s in [-1,1]]+[('p',u,v,a,b) for u,v in pairs for a in range(3) for b in range(3)]
def value(label,w):
 if label[0]=='m':_,u,a,s=label;return s*int(w[u]==a)
 _,u,v,a,b=label;return int(w[u]==a and w[v]==b)
rows=[[value(l,w) for w in words] for l in labels]
expected={o['representative_code']:o['orbit_size'] for o in map(json.loads,(p.parent/'q9-order3-permutation-symmetry/orbits.jsonl').read_text().splitlines())};seen=set();counts={}
for r in map(json.loads,(p/'receipts.jsonl').read_text().splitlines()):
 code=r['code'];assert code not in seen and expected[code]==r['orbit_size'];seen.add(code);z=code;digits=[0]*10
 for i in range(9,-1,-1):digits[i]=z%6;z//=6
 P={}
 for (u,v),z in zip(pairs,digits):P[u,v]=ps[z];P[v,u]=tuple(ps[z].index(a) for a in range(3))
 def cap(u,v,a,b):
  targets=[]
  if a:targets.append(P[u,v][3-a])
  if P[u,v][a]:targets.append(3-P[u,v][a])
  targets += [P[t,v][P[u,t][a]] for t in range(5) if t not in (u,v)]
  return 3-targets.count(b)
 bounds={(u,v,a,b):cap(u,v,a,b) for u,v in pairs for a in range(3) for b in range(3)}
 ids=[i for i,w in enumerate(words) if all(bounds[u,v,w[u],w[v]]>0 for u,v in pairs)]
 rhs=[l[3]*(4,3,3)[l[2]] if l[0]=='m' else bounds[tuple(l[1:])] for l in labels]
 assert len(ids)==r['supported_words']
 if r['status']=='EXACT_INFEASIBLE':
  cert=r['certificate'];assert len(set(i for i,v in cert))==len(cert);assert all(0<=i<120 and v>0 for i,v in cert)
  assert all(sum(v*rows[i][j] for i,v in cert)>=0 for j in ids)
  assert sum(v*rhs[i] for i,v in cert)<0
 elif r['status']=='EXACT_FRACTIONAL_FEASIBLE':
  den=r['denominator'];wit=r['witness'];assert den>0 and len(set(j for j,v in wit))==len(wit);assert all(j in ids and v>0 for j,v in wit)
  assert all(sum(v*rows[i][j] for j,v in wit)<=den*rhs[i] for i in range(120))
 else:raise AssertionError(r['status'])
 counts[r['status']]=counts.get(r['status'],0)+1
assert seen==set(expected)
out={'status':'PASS','cases':len(seen),'counts':counts,'seconds':time.monotonic()-start,'method':'independent path reconstruction and exact integer arithmetic; no solver'}
(p/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
