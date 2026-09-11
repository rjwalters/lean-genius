from pathlib import Path
import itertools,json,hashlib,time
p=Path(__file__).resolve().parent;s=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/order3-n78-local');pins=json.loads((s/'pins.json').read_text())
for n,h in pins.items():assert hashlib.sha256((s/n).read_bytes()).hexdigest()==h
ps=list(itertools.permutations(range(3)));records=json.loads((s/'results.json').read_text());seen=set();counts=[0]*4;no_triples=0;t=time.monotonic()
def mat(perm):return [[int(perm[a]==b) for b in range(3)] for a in range(3)]
def mul(A,B):return [[sum(A[a][k]*B[k][b] for k in range(3)) for b in range(3)] for a in range(3)]
E=[[0,0,0],[0,0,1],[0,1,0]]
for r in records:
 ds=tuple(r['permutations']);assert ds not in seen;seen.add(ds);assert r['status']=='COMPLETE';P={}
 for (u,v),z in zip([(0,1),(0,2),(1,2)],ds):P[u,v]=mat(ps[z]);P[v,u]=list(map(list,zip(*P[u,v])))
 U={}
 for u,v in [(0,1),(0,2),(1,2)]:
  t0=3-u-v;pieces=[mul(E,P[u,v]),mul(P[u,v],E),mul(P[u,t0],P[t0,v])];U[u,v]=[[3-sum(M[a][b] for M in pieces) for b in range(3)] for a in range(3)]
 words=set();triple=False
 for wr in r['words']:
  w=tuple(wr['word']);assert w not in words;words.add(w)
  B=[[3-E[w[u]][a]-sum(P[v,u][w[v]][a] for v in range(3) if v!=u) for a in range(3)] for u in range(3)]
  bound=max(0,min([3]+[U[u,v][w[u]][w[v]] for u,v in [(0,1),(0,2),(1,2)]]))
  if min(map(min,B))<0:bound=0
  if any(w[u]!=0 and B[u]!=[2,2,2] for u in range(3)):bound=min(bound,2)
  assert B==wr['B'] and bound==wr['multiplicity_upper_bound']
  if bound==3:counts[sum(a!=0 for a in w)]+=1;triple=True
 assert words==set(itertools.product(range(3),repeat=3));no_triples+=not triple
assert seen==set(itertools.product(range(6),repeat=3));assert counts==[56,96,48,0] and no_triples==108
out={'status':'PASS','assignment_word_cases':216*27,'triple_bound_counts_by_nonzero_coordinates':counts,'assignments_without_triple_bound':no_triples,'seconds':time.monotonic()-t,'source_pins':pins};(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
