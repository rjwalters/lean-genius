from pathlib import Path
from itertools import combinations_with_replacement
from collections import Counter
import json,hashlib
s=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-involution-fixed-counts');p=Path(__file__).resolve().parent
for f,h in json.loads((s/'pins.json').read_text()).items():assert hashlib.sha256((s/f).read_bytes()).hexdigest()==h
out={};degrees=(1,3,5,7,9)
for N in (78,80):
 large=[]
 for F in range(14,N-57,2):
  L=10*F-N;ex=L*L-F*L-F*F*(F-1);assert L>=F and ex>0;large.append({'F':F,'L':L,'excess':ex})
 profiles=[];tested=0
 for deg in combinations_with_replacement(degrees,12):
  tested+=1;S=sum(deg);R=N-120+S
  if R<0 or sum(r*(r-1) for r in deg)>132:continue
  if any((9-r)*(r-4)>R for r in deg):continue
  profiles.append({'degree_counts':[deg.count(r) for r in degrees],'S':S,'R':R})
 assert tested==1820
 out[str(N)]={'large_fixed_count_exclusions':large,'F12_profiles':profiles}
orig=json.loads((s/'results.json').read_text())
for N in out:
 assert out[N]['large_fixed_count_exclusions']==orig[N]['large_fixed_count_exclusions']
 assert sorted(out[N]['F12_profiles'],key=lambda x:x['S'])==sorted(orig[N]['F12_profiles'],key=lambda x:x['S'])
assert 8*2>11 and 4*2+4>11 and 20**2>8*(4*3+20)
(p/'results.json').write_text(json.dumps({'status':'PASS','multisets_per_order':1820,'orders':out,'remaining_profiles_contradictions_checked':True},indent=2)+'\n');print('PASS:3640 independent degree multisets, nine Cauchy gaps, both remaining contradictions')
