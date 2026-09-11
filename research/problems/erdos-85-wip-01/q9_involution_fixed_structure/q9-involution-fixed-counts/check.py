from pathlib import Path
import itertools,json
p=Path(__file__).resolve().parent;out={}
for N in [78,80]:
 large=[]
 for F in range(14,N-58+1,2):
  L=10*F-N;excess=L*L-F*L-F*F*(F-1);assert excess>0;large.append({'F':F,'L':L,'excess':excess})
 profiles=[];d=[1,3,5,7,9]
 for a,b,c,e in itertools.product(range(13),repeat=4):
  f=12-a-b-c-e
  if f<0:continue
  counts=[a,b,c,e,f];S=sum(x*y for x,y in zip(counts,d));R=N-120+S
  if R<0 or sum(x*y*(y-1) for x,y in zip(counts,d))>132:continue
  if any((9-r)*(r-4)>R for n,r in zip(counts,d) if n):continue
  profiles.append({'degree_counts':counts,'S':S,'R':R})
 out[N]={'large_fixed_count_exclusions':large,'F12_profiles':profiles}
assert out[78]['F12_profiles']==[]
assert {tuple(x['degree_counts']) for x in out[80]['F12_profiles']}=={(0,8,4,0,0),(1,10,0,0,1)}
(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
