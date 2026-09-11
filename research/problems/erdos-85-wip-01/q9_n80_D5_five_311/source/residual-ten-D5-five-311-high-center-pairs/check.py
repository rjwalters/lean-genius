from pathlib import Path
import json,itertools as it,time,functools
p=Path(__file__).resolve().parent;b=p.parent;start=time.monotonic();data=json.loads((b/'residual-ten-D5-five-311-center-cross-domains/results.json').read_text())['records'];prior={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-center-cross-cover/results.json').read_text())['records']};original={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-center-domains/results.json').read_text())['records']};prop={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-low-propagation/results.json').read_text())['records']};edgecases={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-low-edge-capacity/results.json').read_text())['records']};joint={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-nonempty-joint/results.json').read_text())['records']};graphs={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-high-matchings/results.json').read_text())['records']};out=[]
for r in data:
 if prior[r['root']]['witness'] is None:continue
 assert time.monotonic()-start<30
 o=original[r['root']];src=o['source_root'];ai=o['source_assignment'];lows=next(a['lows'] for a in edgecases[src]['survivors'] if a['assignment']==ai);a=next(a for a in prop[src]['survivors'] if a['assignment']==ai);source=joint[src];Hg=graphs[source['packing_root']]['survivors'][source['graph']]['edges'];matched={v//2 for e in Hg for v in e};forced=[set() for _ in range(60)]
 def edge(v,w):forced[v].add(w);forced[w].add(v)
 for v,w in Hg:edge(v,w)
 for i,(v,t) in enumerate(lows):
  if v>=0:edge(v,10+i)
 for i,j in a['forced_edges']:edge(10+i,10+j)
 possible=[set(x) for x in forced]
 for i,j in a['remaining_edges']:possible[10+i].add(10+j);possible[10+j].add(10+i)
 groups=[[set([2*f,2*f+1]+[10+v for oi in g for v in o['low_orbits'][oi]]) for g in ds] for f,ds in enumerate(r['high_groups'])];degrees=[[1+sum(lows[o['low_orbits'][oi][0]][0]<0 for oi in g)-int(f in matched) for g in ds] for f,ds in enumerate(r['high_groups'])];pairs=[]
 for f,g in it.combinations(range(5),2):
  for i,A in enumerate(groups[f]):
   for j,B in enumerate(groups[g]):
    assert time.monotonic()-start<30
    bits=0
    if not A&B:
     cross=[(v,w) for v in A for w in forced[v]&B];bits=0 if cross else 2;usedA={v for v,w in cross};usedB={w for v,w in cross}
     if len(usedA)==len(cross)==len(usedB):
      left=sorted(A-usedA);right=sorted(B-usedB);required=sum(1<<q for q,w in enumerate(right) if w>=10)
      @functools.lru_cache(None)
      def matching(k,used):
       if k==len(left):return used&required==required
       v=left[k]
       if v<10 and matching(k+1,used):return True
       return any(not used>>q&1 and w in possible[v] and matching(k+1,used|1<<q) for q,w in enumerate(right))
      if matching(0,0):bits|=1
    pairs.append([f,g,i,j,bits])
 out.append({'root':r['root'],'degrees':degrees,'pair_domains':pairs})
r={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'seconds':r['seconds'],'cases':len(out),'pairs':sum(len(r['pair_domains']) for r in out),'neither':sum(x[-1]==0 for r in out for x in r['pair_domains'])}))
