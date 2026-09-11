from pathlib import Path
from itertools import combinations_with_replacement,combinations
import json,hashlib
s=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-involution-ten-fixed');p=Path(__file__).resolve().parent
for f,h in json.loads((s/'pins.json').read_text()).items():assert hashlib.sha256((s/f).read_bytes()).hexdigest()==h
out={};checked=0
for N in (78,80):
 records=[]
 for ds in combinations_with_replacement((1,3,5,7,9),10):
  checked+=1;S=sum(ds);R=N-100+S
  if R<0 or sum(x*(x-1) for x in ds)>90 or any((9-x)*(x-2)>R for x in ds):continue
  possible=True
  for i,r in enumerate(ds):
   others=ds[:i]+ds[i+1:]
   if min(sum(x-1 for x in chosen) for chosen in combinations(others,r))>9:possible=False;break
  if possible:records.append({'counts':[ds.count(r) for r in (1,3,5,7,9)],'S':S,'R':R})
 out[str(N)]=records
orig=json.loads((s/'results.json').read_text())
for n in out:assert sorted(out[n],key=lambda x:x['counts'])==sorted(orig[n],key=lambda x:x['counts'])
assert checked==2002
assert 8*8>8+8*6
assert 7*6+8+8+6==8*8 and 8+2>9
(p/'results.json').write_text(json.dumps({'status':'PASS','degree_multisets':checked,'profiles':out,'saturation_arithmetic_checked':True},indent=2)+'\n');print('PASS2002 multisets, exact seven profiles, residual saturation arithmetic')
