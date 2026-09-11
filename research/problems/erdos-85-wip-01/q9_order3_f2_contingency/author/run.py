import itertools,json,time
from pathlib import Path
p=Path(__file__).parent;start=time.monotonic(); cap=60;records=[];stop=False
for k in (2,3):
 for dom in itertools.combinations(range(3),k):
  for target in itertools.permutations(range(3),k):
   P=[[0]*3 for _ in range(3)];mapping=[-1]*3
   for a,b in zip(dom,target):P[a][b]=1;mapping[a]=b
   C=[[3-(P[3-a][b] if a else 0)-(P[a][3-b] if b else 0) for b in range(3)] for a in range(3)]
   ra=[8-int(a!=0)-sum(P[a]) for a in range(3)];rb=[8-int(b!=0)-sum(P[a][b] for a in range(3)) for b in range(3)]
   cases=[None] if k==2 else [None]+list(itertools.product(range(3),repeat=2))
   for missing in cases:
    r=ra[:];s=rb[:]
    if missing is not None:r[missing[0]]-=1;s[missing[1]]-=1
    count=0;tables=[]
    rows=[[q for q in itertools.product(*(range(c+1) for c in C[a])) if sum(q)==r[a]] for a in (0,1)]
    for row0,row1 in itertools.product(*rows):
     if time.monotonic()-start>=cap:stop=True;break
     row2=[s[b]-row0[b]-row1[b] for b in range(3)]
     if sum(row2)==r[2] and all(0<=row2[b]<=C[2][b] for b in range(3)):
      count+=1;tables.append([row0,row1,row2])
    records.append({'cross_orbits':k,'mapping':mapping,'missing_labels':missing,'row_margins':r,'column_margins':s,'capacities':C,'status':'UNKNOWN' if stop else 'COMPLETE','count':count,'tables':tables})
    if stop:break
   if stop:break
  if stop:break
 if stop:break
result={'status':'UNKNOWN' if stop else 'COMPLETE','original_wall_cap':cap,'seconds':time.monotonic()-start,'states':len(records),'zero_states':sum(r['count']==0 for r in records),'tables':sum(r['count'] for r in records)}
(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');(p/'receipts.json').write_text(json.dumps(records)+'\n');print(json.dumps(result))
