from pathlib import Path
from itertools import permutations,product
import json,hashlib
src=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/involution-n78-triangle-missing-parity');out=Path(__file__).parent
pins=json.loads((src/'pins.json').read_text())
for n,h in pins.items():assert hashlib.sha256((src/n).read_bytes()).hexdigest()==h,n
premise=json.loads((src/'premise.json').read_text());print('Premise:',premise)
if 'source' in premise:assert hashlib.sha256(Path(premise['source']).read_bytes()).hexdigest()==premise['sha256']
perms=[g for g in permutations(range(6)) if all(g[i^1]==(g[i]^1) for i in range(6))]
def parity(g):return sum(g[i]>g[j] for i in range(6) for j in range(i+1,6))%2
def epsilon(g):return sum(g[i]&1 for i in (0,2,4))%2
assert len(perms)==48 and sum(parity(g) for g in perms)==24
for g in perms:
 assert parity(g)==epsilon(g)
 inv=tuple(g.index(i) for i in range(6));assert epsilon(inv)==epsilon(g)
 for h in perms:
  comp=tuple(g[h[i]] for i in range(6));assert epsilon(comp)==(epsilon(g)+epsilon(h))%2
for t,s in product(range(2),repeat=2):
 triple=(0,t,s);image=(1,t^1,s^1)
 xy=next(v for v in (triple,image) if v[0]==0)[1]
 xz=next(v for v in (triple,image) if v[0]==0)[2]
 yz=next(v for v in (triple,image) if v[1]==0)[2]
 assert (xy,xz,yz)==(t,s,t^s) and xy^xz^yz==0
result={'status':'PASS','source_pins':len(pins),'centralizer':48,'odd_permutations':24,'composition_checks':2304,'triple_bit_cases':4,'scope':'Independent finite sign/bit checks supplement full general paper parity proof; no triple or graph existence claim'}
(out/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
(out/'input-pins.json').write_text(json.dumps({str(src/'pins.json'):hashlib.sha256((src/'pins.json').read_bytes()).hexdigest()},indent=2)+'\n')
