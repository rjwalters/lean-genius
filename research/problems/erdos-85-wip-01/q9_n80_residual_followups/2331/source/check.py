from pathlib import Path
import itertools,json
p=Path(__file__).resolve().parent
excluded={(0,1,3,3,3),(0,2,2,3,3),(1,1,2,3,3),(1,2,2,2,3),(0,2,2,2,3),(1,1,1,3,3),(1,2,2,3,3)}
allowed=[]
for ds in itertools.combinations_with_replacement(range(4),5):
 if sum(ds)>10 or ds in excluded:continue
 z=ds.count(0)
 if z==0 and (ds.count(1)<1 or ds.count(3)>2):continue
 if z==2 and sum(ds)>7:continue
 allowed.append(ds)
assert max(map(sum,allowed))==9
eq=[d for d in allowed if sum(d)==9]
assert eq==[(0,1,2,3,3),(1,1,2,2,3),(1,2,2,2,2)]
r={'sorted_tuples_in_full_domain':56,'maximum_residual_edges':9,'equality_patterns':eq,'scope':'Arithmetic audit of accepted constraints only.'}
(p/'verification.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
