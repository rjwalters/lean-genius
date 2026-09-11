from pathlib import Path
import itertools,json,hashlib,time
ROOT=Path(__file__).resolve().parent
start=time.monotonic()
bases=[Path('/tmp/erdos85-sol1-q9-n78-faithful-cayley'),Path('/tmp/erdos85-sol1-q9-n78-faithful-cayley-certificates'),Path('/tmp/erdos85-sol1-q9-n78-three-orbit-stabilizers'),Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n78-automorphism-order-orbits')]
pins={}
for base in bases:
 for name,h in json.loads((base/'pins.json').read_text()).items():
  f=base/name;assert hashlib.sha256(f.read_bytes()).hexdigest()==h
  pins[str(f)]=h
 pins[str(base/'pins.json')]=hashlib.sha256((base/'pins.json').read_bytes()).hexdigest()
# Independent construction: permute the three matching edges and orient each image.
G=set()
for perm in itertools.permutations(range(3)):
 for bits in itertools.product(range(2),repeat=3):
  G.add(tuple(2*perm[i//2]+((i%2)^bits[i//2]) for i in range(6)))
assert len(G)==48
identity=tuple(range(6))
def inverse(g):return tuple(g.index(i) for i in range(6))
def compose(g,h):return tuple(g[h[i]] for i in range(6))
# Independent cover: select exactly one element from each required target fiber.
fibers=[[g for g in G if g[0]==i] for i in [0,2,3,4,5]]
assert list(map(len,fibers))==[8]*5
cover=set();tuples=0
for choice in itertools.product(*fibers):
 tuples+=1
 assert time.monotonic()-start<30
 S=frozenset(choice)
 if identity in S:continue
 if frozenset(inverse(g) for g in S)==S:cover.add(S)
assert tuples==32768 and len(cover)==380
saved=json.loads((bases[1]/'certificates.json').read_text())
assert set(map(tuple,saved['group']))==G
order=list(map(tuple,saved['group']));seen=set();edge_checks=0
for cert in saved['certificates']:
 S=frozenset(order[i] for i in cert['S']);cycle=[order[i] for i in cert['cycle']]
 assert S in cover and S not in seen;seen.add(S)
 assert len(cycle)==4 and len(set(cycle))==4
 for a,b in zip(cycle,cycle[1:]+cycle[:1]):
  assert compose(inverse(a),b) in S;edge_checks+=1
assert seen==cover and edge_checks==1520
source=json.loads((bases[0]/'results.json').read_text())
assert source['status']=='COMPLETE' and source['target_survivors']==380 and source['surviving_sets']==[]
# The total inverse-closed count follows independently from element orders.
involutions=sum(g!=identity and inverse(g)==g for g in G)
pairs=(48-1-involutions)//2
from math import comb
assert involutions==19 and pairs==14
assert comb(19,5)+14*comb(19,3)+comb(14,2)*19==source['inverse_closed_sets']==26923
(ROOT/'input-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
result=dict(group_size=48,target_tuples=tuples,inverse_closed_target_sets=380,distinct_C4_certificates=380,directed_edges_checked=edge_checks,seconds=time.monotonic()-start,scope='Independent target-fiber cover plus all W-only C4 certificates; no producer search replay')
(ROOT/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
