from pathlib import Path
import hashlib,json,itertools
p=Path(__file__).resolve().parent;s=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/order3-n78-quotient');pins=json.loads((s/'pins.json').read_text())
for name,h in pins.items():assert hashlib.sha256((s/name).read_bytes()).hexdigest()==h
survivors=[]
for b in itertools.product(range(4),repeat=3):
 if sum(b)!=6:continue
 ds=[d for d in itertools.product(range(4),repeat=3) if sum(d)<=3 and all(3*b[a]<=(6,5,5)[a]+d[a] for a in range(3))]
 if ds:survivors.append({'b':b,'double_allocations':ds})
assert [x['b'] for x in survivors]==[(2,2,2)]
profiles=[(s,d) for s in range(17) for d in range(17-s) if s+2*d==6 and s+4*d<=8]
assert profiles==[(4,1),(6,0)]
assert all(s+d>=5 for s,d in profiles)
result={'status':'PASS','source_pins':pins,'row_profiles_singles_doubles':profiles,'balanced_margins':survivors,'multiplicity_bound':16//5,'attached_total_walks':16+2+2+3}
(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
