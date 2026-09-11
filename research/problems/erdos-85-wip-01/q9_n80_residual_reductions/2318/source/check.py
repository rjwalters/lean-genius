from pathlib import Path
import itertools,json
p=Path(__file__).resolve().parent
allowed=[];tested=0
for ds in itertools.combinations_with_replacement(range(4),5):
 tested+=1
 if 0 in ds:
  if sum(ds)>10:continue # accepted2293
 else:
  if ds.count(1)<1 or ds.count(3)>2:continue # accepted2297
  if ds==(1,2,2,3,3):continue # accepted2303
 allowed.append(ds)
assert max(map(sum,allowed))==10
equality=[ds for ds in allowed if sum(ds)==10]
assert equality==[(0,1,3,3,3),(0,2,2,3,3),(1,1,2,3,3),(1,2,2,2,3)]
result={'tested_sorted_degree_tuples':tested,'maximum_residual_edges':10,'equality_patterns':equality,'scope':'Arithmetic consequence of accepted bounds; no graph enumeration.'}
(p/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
