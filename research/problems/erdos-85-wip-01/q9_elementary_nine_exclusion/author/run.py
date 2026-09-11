import itertools,math,json,time
from pathlib import Path
p=Path(__file__).parent;start=time.monotonic();lines=range(4);pairs=list(itertools.combinations(lines,2));cap=60
# Fix kernels of the two short stabilizers as lines0 and1.
first=[]
for u,v,w in itertools.product(lines,repeat=3):
 sig=[]
 for k in lines:
  x=8-(2 if k==u else -1);y=8-(2 if k==v else -1);t=4 if k==w else 1
  sig.append((9*x-3)*y-9*t if k==0 else (9*y-3)*x-9*t if k==1 else x*y-t)
 first.append(((u,v,w),sig))
second=[(s,[(8-(1 if k in s else -2))**2-1 for k in lines]) for s in pairs]
third=[]
for u in lines:
 for ss in itertools.product(pairs,repeat=3):
  sig=[]
  for k in lines:
   z=8-(2 if k==u else -1);v=[8-(1 if k in s else -2) for s in ss]
   sig.append(z*math.prod(v)-sum(math.prod(v[j] for j in range(3) if j!=i) for i in range(3)))
  third.append(((u,ss),sig))
visited=0;retained=[];hist=[0]*5;stop=False
for f,fs in first:
 for s,ss in second:
  for t,ts in third:
   if time.monotonic()-start>=cap:stop=True;break
   visited+=1;values=[fs[k]*ss[k]*ts[k] for k in lines];fail=next((k for k,n in enumerate(values) if n<0 or math.isqrt(n)**2!=n),4);hist[fail]+=1
   if fail==4:retained.append({'first':f,'second':s,'third':t,'determinants':values})
  if stop:break
 if stop:break
r={'status':'UNKNOWN' if stop else 'COMPLETE','original_wall_cap':cap,'seconds':time.monotonic()-start,'expected':len(first)*len(second)*len(third),'visited':visited,'first_failed_character_histogram':hist,'retained_count':len(retained)}
(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');(p/'retained.json').write_text(json.dumps(retained)+'\n');print(json.dumps(r))
