from pathlib import Path
import itertools,json,time
p=Path(__file__).resolve().parent;start=time.monotonic();words=list(itertools.product(range(3),repeat=5));ps=list(itertools.permutations(range(3)));pairs=list(itertools.combinations(range(5),2));records=[json.loads(x) for x in (p/'receipts.jsonl').read_text().splitlines()];expected={r['code'] for r in map(json.loads,(p.parent/'q9-order3-color-lp-cover/receipts.jsonl').read_text().splitlines()) if r['status']=='EXACT_FRACTIONAL_FEASIBLE'}
assert {r['code'] for r in records}==expected and len(records)==len(expected)
lines=(p/'input.txt').read_text().splitlines();assert int(lines[0])==len(records);positive=0
for line,r in zip(lines[1:],records):
 data=list(map(int,line.split()));code,n=data[:2];assert code==r['code'];z=code;ds=[0]*10
 for i in range(9,-1,-1):ds[i]=z%6;z//=6
 P={}
 for (u,v),z in zip(pairs,ds):P[u,v]=ps[z];P[v,u]=tuple(ps[z].index(a) for a in range(3))
 def cap(u,v,a,b):
  paths=[]
  if a:paths.append(P[u,v][3-a])
  if P[u,v][a]:paths.append(3-P[u,v][a])
  paths += [P[t,v][P[u,t][a]] for t in range(5) if t not in (u,v)]
  return 3-paths.count(b)
 U={(u,v,a,b):cap(u,v,a,b) for u,v in pairs for a in range(3) for b in range(3)}
 def good(w):
  if not all(U[u,v,w[u],w[v]]>0 for u,v in pairs):return False
  for u in range(5):
   targets=[P[v,u][w[v]] for v in range(5) if v!=u]
   if w[u]:targets.append(3-w[u])
   if any(targets.count(a)>3 for a in range(3)):return False
  return True
 ids=[i for i,w in enumerate(words) if good(w)]
 assert ids==data[2:2+n] and [U[u,v,a,b] for u,v in pairs for a in range(3) for b in range(3)]==data[2+n:]
 if r['status']=='INTEGER_COLORING':
  chosen=r['words'];assert len(chosen)==len(set(chosen))==10 and all(i in ids for i in chosen);ws=[words[i] for i in chosen]
  assert all(sum(w[u]==a for w in ws)==(4,3,3)[a] for u in range(5) for a in range(3))
  assert all(sum(x==y for x,y in zip(w,z))<=3 for w,z in itertools.combinations(ws,2))
  assert all(sum(w[u]==a and w[v]==b for w in ws)<=U[u,v,a,b] for u,v in pairs for a in range(3) for b in range(3));positive+=1
 else:assert r['status']=='COMPLETE_NEGATIVE' and r['nodes']<=100000 and not r['words']
out={'status':'PASS_INPUTS_AND_POSITIVES','cases':len(records),'integer_witnesses_verified':positive,'negative_cases_pending_independent_search':len(records)-positive,'seconds':time.monotonic()-start};(p/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
