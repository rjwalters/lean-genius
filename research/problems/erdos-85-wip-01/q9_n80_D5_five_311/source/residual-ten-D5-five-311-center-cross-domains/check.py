from pathlib import Path
import json,itertools as it,time,functools
p=Path(__file__).resolve().parent;b=p.parent;start=time.monotonic();data=json.loads((b/'residual-ten-D5-five-311-center-domains/results.json').read_text())['records'];prior={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-structured-center-cover/results.json').read_text())['records']};prop={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-low-propagation/results.json').read_text())['records']};edgecases={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-low-edge-capacity/results.json').read_text())['records']};joint={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-nonempty-joint/results.json').read_text())['records']};graphs={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-high-matchings/results.json').read_text())['records']};out=[]
def guard():
 if time.monotonic()-start>=30:raise TimeoutError
for d in data:
 if d['root'] not in prior:continue
 guard();src=d['source_root'];ai=d['source_assignment'];lows=next(a['lows'] for a in edgecases[src]['survivors'] if a['assignment']==ai);a=next(a for a in prop[src]['survivors'] if a['assignment']==ai);source=joint[src];Hg=graphs[source['packing_root']]['survivors'][source['graph']]['edges'];forced=[set() for _ in range(60)]
 def edge(i,j):forced[i].add(j);forced[j].add(i)
 for v,w in Hg:edge(v,w)
 for i,(v,r) in enumerate(lows):
  if v>=0:edge(v,10+i)
 for i,j in a['forced_edges']:edge(10+i,10+j)
 possible=[set(x) for x in forced]
 for i,j in a['remaining_edges']:possible[10+i].add(10+j);possible[10+j].add(10+i)
 colors=[lows[pair[0]][0]//2 if lows[pair[0]][0]>=0 else -1 for pair in d['low_orbits']];high=[[{'orbits':g,'vertices':[2*f,2*f+1]+[10+v for i in g for v in d['low_orbits'][i]]} for g in ds] for f,ds in enumerate(d['high_groups'])];low=[]
 for gi,g in enumerate(d['low_groups']):
  cs=[colors[i] for i in g];z=cs.count(-1);A=sum(1<<v for v in set(cs) if v>=0)
  if z<=1 and A.bit_count()==3-z:low.append({'source_group':gi,'orbits':g,'active':A,'inactive':z,'vertices':[10+v for i in g for v in d['low_orbits'][i]]})
 compatibility=[];tests=0
 for f,ds in enumerate(high):
  lists=[]
  for h in ds:
   H=set(h['vertices']);accepted=[]
   for li,l in enumerate(low):
    guard();tests+=1;L=set(l['vertices'])
    if H&L:continue
    crosses={(v,w) for v in H for w in forced[v]&L}
    if not l['active']>>f&1:
     if not crosses:accepted.append(li)
     continue
    if any(sum(v==x for v,w in crosses)>1 for x in H) or any(sum(w==x for v,w in crosses)>1 for x in L):continue
    usedH={v for v,w in crosses};usedL={w for v,w in crosses};left=sorted(H-usedH);right=sorted(L-usedL);assert len(left)==len(right)
    @functools.lru_cache(None)
    def match(i,used):
     if i==len(left):return True
     return any(not used>>j&1 and w in possible[left[i]] and match(i+1,used|1<<j) for j,w in enumerate(right))
    if match(0,0):accepted.append(li)
   lists.append(accepted)
  compatibility.append(lists)
 out.append({'root':d['root'],'high_groups':[[h['orbits'] for h in ds] for ds in high],'low_groups':[{k:v for k,v in l.items() if k!='vertices'} for l in low],'compatibility':compatibility,'tested':tests})
r={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'seconds':r['seconds'],'cases':len(out),'tested':sum(r['tested'] for r in out),'compatible':sum(len(x) for r in out for ds in r['compatibility'] for x in ds)}))
