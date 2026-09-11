from pathlib import Path
import json,itertools as it,time,functools
p=Path(__file__).resolve().parent;b=p.parent;start=time.monotonic();models={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-low-orbit-capacity/models.json').read_text())['records']};results=json.loads((b/'residual-ten-D5-five-311-low-orbit-capacity/results.json').read_text())['records'];prop={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-low-propagation/results.json').read_text())['records']};edgecases={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-low-edge-capacity/results.json').read_text())['records']};joint={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-nonempty-joint/results.json').read_text())['records']};graphs={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-high-matchings/results.json').read_text())['records']};pack=json.loads((b/'residual-ten-D5-five-311-packing/results.json').read_text())['records'];dom=json.loads((b/'residual-ten-D5-supports/results.json').read_text())['records'];out=[]
def guard():
 if time.monotonic()-start>=30:raise TimeoutError
for result in results:
 if result['status']!='EXACT_RATIONAL_WITNESS':continue
 guard();m=models[result['root']];src=m['source_root'];ai=m['assignment'];lows=next(x['lows'] for x in edgecases[src]['survivors'] if x['assignment']==ai);a=next(x for x in prop[src]['survivors'] if x['assignment']==ai);source=joint[src];ci=source['class'];root=pack[ci]['survivors'][source['source_root']];c=dom[ci];ss=[c['high3'][j] for j in root['high3']];S=[set(t) for s in ss for t in (s,[e^1 for e in s])];Hg=graphs[source['packing_root']]['survivors'][source['graph']]['edges'];tau=m['low_tau'];orbits=[(i,tau[i]) for i in range(50) if i<tau[i]];types=[lows[i][1]//2 for i,j in orbits];N=[set() for _ in range(70)]
 def edge(v,w):N[v].add(w);N[w].add(v)
 for v,w in c['edges']:edge(v,w)
 for v,s in enumerate(S):
  for r in s:edge(10+v,r)
 for v,w in Hg:edge(10+v,10+w)
 for i,(v,r) in enumerate(lows):
  edge(20+i,r)
  if v>=0:edge(20+i,10+v)
 for i,j in a['forced_edges']:edge(20+i,20+j)
 possible=[set(x) for x in N]
 for i,j in a['remaining_edges']:possible[20+i].add(20+j);possible[20+j].add(20+i)
 masks=[sum(1<<v for v in ns) for ns in N]
 def group(vs):
  if any(masks[v]&masks[w] for v,w in it.combinations(vs,2)):return False
  vs=set(vs);internal={v:N[v]&vs for v in vs}
  if any(len(ns)>1 for ns in internal.values()):return False
  used={v for v,ns in internal.items() if ns};remaining=vs-used
  @functools.lru_cache(None)
  def cover(rem):
   required=[v for v in rem if v>=20]
   if not required:return True
   v=required[0]
   return any(w!=v and w in possible[v] and cover(tuple(z for z in rem if z!=v and z!=w)) for w in rem)
  return cover(tuple(sorted(remaining)))
 high=[]
 for v in range(0,10,2):
  missing=set(range(5))-{e//2 for e in S[v]};assert len(missing)==2;left,right=sorted(missing);choices=[]
  for i in range(25):
   if types[i]!=left:continue
   for j in range(25):
    if types[j]==right and group([10+v,10+(v^1)]+[20+x for t in [i,j] for x in orbits[t]]):choices.append([i,j])
  high.append(choices)
 low=[]
 for chosen in it.combinations(range(25),3):
  guard()
  if len({types[i] for i in chosen})==3 and group([20+x for t in chosen for x in orbits[t]]):low.append(chosen)
 out.append({'root':m['root'],'source_root':src,'source_assignment':ai,'class':ci,'low_orbits':orbits,'support_types':types,'high_groups':high,'low_groups':low})
r={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'seconds':r['seconds'],'cases':len(out),'empty_high_group_cases':sum(any(not g for g in r['high_groups']) for r in out),'high_options':sum(len(g) for r in out for g in r['high_groups']),'low_options':sum(len(r['low_groups']) for r in out)}))
