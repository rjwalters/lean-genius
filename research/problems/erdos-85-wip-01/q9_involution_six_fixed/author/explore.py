from itertools import combinations
import json,time
from pathlib import Path
start=time.monotonic(); edges=list(combinations(range(6),2));out={78:{},80:{}}
for mask in range(1<<15):
 if time.monotonic()-start>30:raise RuntimeError('Original 30-second cap reached; UNKNOWN')
 ns=[0]*6
 for k,(u,v) in enumerate(edges):
  if mask>>k&1:ns[u]|=1<<v;ns[v]|=1<<u
 ds=[x.bit_count() for x in ns]
 if any(d%2==0 for d in ds):continue
 if any((ns[u]&ns[v]).bit_count()>1 for u,v in edges):continue
 for N in out:
  R=N-60+sum(ds)
  if any((9-d)*(2+d)>R for d in ds):continue
  key=','.join(map(str,sorted(ds)))
  t=out[N].setdefault(key,{'count':0,'representative_edges':[list(e) for k,e in enumerate(edges) if mask>>k&1]});t['count']+=1
result={'status':'COMPLETE','cap_seconds':30,'labelled_graphs':32768,'elapsed_seconds':time.monotonic()-start,'survivors_by_order':out}
Path(__file__).with_name('explore-results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
