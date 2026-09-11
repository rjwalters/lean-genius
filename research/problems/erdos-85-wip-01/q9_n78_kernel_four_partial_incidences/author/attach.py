from pathlib import Path
import json,itertools as I,time
p=Path(__file__).parent;prior=json.loads((p/'results.json').read_text());extension=json.loads((p/'extension-results.json').read_text());assert prior['status']==extension['status']=='COMPLETE';els=list(map(tuple,prior['elements']));ix={x:i for i,x in enumerate(els)}
def mul(x,y):
 i,j=els[x];k,l=els[y];return ix[(i+(5 if j else 1)*k)%8,j^l]
M=[[mul(x,y) for y in range(16)] for x in range(16)];cosets=prior['cosets'];cx={g:i for i,C in enumerate(cosets) for g in C}
start=time.monotonic();status='INCOMPLETE';out=[]
try:
 for ei,ext in enumerate(extension['records']):
  if ext['c4'] is not None:continue
  rec=prior['records'][ext['source']];d,xp,D=(rec[k] for k in ['d','xp','D']);neighbors=[[] for _ in range(24)]
  for g,(i,j) in enumerate(els):
   for r in [cx[M[g][cosets[xp][0]]],8+g,8+M[g][d]]:neighbors[r].append((0,g))
   for h in D:neighbors[8+M[g][h]].append((2,g))
   for r in [8+g]+[cx[M[g][cosets[k][0]]] for k in ext['pair']]:neighbors[r].append((1,g))
  assert all(len(ns)==6 for ns in neighbors)
  for delta in range(4):
   if time.monotonic()-start>30:raise TimeoutError
   failure=None
   for r,ns in enumerate(neighbors):
    seen={}
    for w,g in ns:
     i,j=els[g];s=j if w==0 else 2+(((i%2)*2+j)^(delta if w==2 else 0))
     if s in seen:failure={'residual':r,'center':s,'W': [seen[s],[w,g]]};break
     seen[s]=[w,g]
    if failure:break
   out.append({'extension_source':ei,'delta':delta,'collision':failure})
 status='COMPLETE'
except TimeoutError:pass
result={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'attachment-results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':status,'seconds':result['seconds'],'cases':len(out),'positive':sum(x['collision'] is None for x in out)}))
