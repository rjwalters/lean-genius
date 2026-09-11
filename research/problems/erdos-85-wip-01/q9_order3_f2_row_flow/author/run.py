import json,time,collections,hashlib
from pathlib import Path
p=Path(__file__).parent;src=Path('/tmp/erdos85-sol1-q9-order3-f2-contingency/receipts.json');input=json.loads(src.read_text());start=time.monotonic();cap=60
calls=0
# integral maxflow: source0, left1..4, right5..8, sink9

def flow(n,ba,bb,need):
 global calls
 calls+=1
 if min(ba+bb)<0:return -1
 c=[[0]*10 for _ in range(10)]
 for a in range(4):c[0][1+a]=ba[a]
 for b in range(4):c[5+b][9]=bb[b]
 for (a,b),v in n.items():c[1+a][5+b]=v
 f=0
 while f<need:
  prev=[-1]*10;prev[0]=0;queue=collections.deque([0])
  while queue and prev[9]<0:
   u=queue.popleft()
   for v in range(10):
    if c[u][v]>0 and prev[v]<0:prev[v]=u;queue.append(v)
  if prev[9]<0:break
  z=need-f;v=9
  while v:z=min(z,c[prev[v]][v]);v=prev[v]
  v=9
  while v:u=prev[v];c[u][v]-=z;c[v][u]+=z;v=u
  f+=z
 return f

def supported(n,w,mapping):
 a,b=w;degree=9-int(a<3)-int(b<3)
 ba=[3-int(a>0 and a<3 and x==3-a)-int(b<3 and mapping[x]==b) for x in range(3)]+[degree]
 bb=[3-int(b>0 and b<3 and y==3-b)-int(a<3 and mapping[a]==y) for y in range(3)]+[degree]
 base=n.copy();base[w]-=1
 outcomes=[{'double':None,'flow':flow(base,ba,bb,degree),'need':degree}]
 if outcomes[-1]['flow']==degree:return True,outcomes
 for v,count in n.items():
  options=[True] if v==w else [False]
  if v==w and count>1:options.append(False)
  for selfloop in options:
   remaining=base.copy()
   if not selfloop:remaining[v]-=1
   if min(remaining.values())<0:continue
   # Two positively used targets sharing both attached labels cannot include a2.
   if v[0]<3 and v[1]<3:remaining[v]=0
   aa=ba[:];bb2=bb[:];aa[v[0]]-=2;bb2[v[1]]-=2
   f=flow(remaining,aa,bb2,degree-2)
   outcomes.append({'double':v,'selfloop':selfloop,'flow':f,'need':degree-2})
   if f==degree-2:return True,outcomes
 return False,outcomes
receipts=[];stopped=False
for sid,r in enumerate(input):
 for tid,T in enumerate(r['tables']):
  if time.monotonic()-start>=cap:stopped=True;break
  n={(a,b):T[a][b] for a in range(3) for b in range(3) if T[a][b]}
  if r['cross_orbits']==3:
   missing=r['missing_labels']
   if missing is None:n[3,3]=1
   else:i,j=missing;n[i,3]=1;n[3,j]=1
  assert sum(n.values())==20
  tests=[];ok=True
  for w in sorted(n):
   valid,trials=supported(n,w,r['mapping']);tests.append({'word':w,'supported':valid,'trials':trials})
   if not valid:ok=False;break
  receipts.append({'state':sid,'table':tid,'status':'RETAINED' if ok else 'EXCLUDED','tests':tests})
 if stopped:break
res={'status':'UNKNOWN' if stopped else 'COMPLETE','original_wall_cap':cap,'seconds':time.monotonic()-start,'tables':len(receipts),'excluded':sum(x['status']=='EXCLUDED' for x in receipts),'retained':sum(x['status']=='RETAINED' for x in receipts),'flow_calls':calls}
(p/'results.json').write_text(json.dumps(res,indent=2)+'\n');(p/'receipts.json').write_text(json.dumps(receipts)+'\n');(p/'input-pin.json').write_text(json.dumps({'path':str(src),'sha256':hashlib.sha256(src.read_bytes()).hexdigest()},indent=2)+'\n');print(json.dumps(res))
