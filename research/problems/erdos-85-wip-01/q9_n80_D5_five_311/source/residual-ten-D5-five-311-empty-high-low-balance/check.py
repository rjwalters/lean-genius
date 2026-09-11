from pathlib import Path
import json,itertools as it,time
p=Path(__file__).resolve().parent;b=p.parent;start=time.monotonic();data=json.loads((b/'residual-ten-D5-five-311-empty-high-joint/results.json').read_text())['records'];pack=json.loads((b/'residual-ten-D5-five-311-packing/results.json').read_text())['records'];dom=json.loads((b/'residual-ten-D5-supports/results.json').read_text())['records'];out=[]
def flip(m):return sum(1<<(i^1) for i in range(10) if m>>i&1)
for source in data:
 ci=source['class'];root=pack[ci]['survivors'][source['source_root']];c=dom[ci];rho={v:w for a,z in c['edges'] for v,w in [(a,z),(z,a)]};ss=[c['high3'][j] for j in root['high3']];S=[set(t) for s in ss for t in (s,[e^1 for e in s])];rec={'root':source['root'],'packing_root':source['packing_root'],'class':ci,'source_root':source['source_root'],'certificates':[],'survivors':[]};out.append(rec)
 for ai,selected in enumerate(source['survivors']):
  assert time.monotonic()-start<30
  rows=[x for m in selected for x in (m,flip(m))];lows=[(v,r) for v in range(10) for r in range(10) if r not in {rho[e] for e in S[v]} and not(rows[v]>>r&1)];assert len(lows)==50
  demand=[[0]*10 for _ in range(10)]
  for v,r in lows:
   targets=set(range(10))-({rho[r]}|S[v]);assert len(targets)==6
   for e in targets:demand[r][e]+=1
  bad=next(((r,e) for r,e in it.combinations(range(10),2) if demand[r][e]!=demand[e][r]),None)
  if bad:
   r,e=bad;rec['certificates'].append({'assignment':ai,'kind':'asymmetric','pair':[r,e],'counts':[demand[r][e],demand[e][r]]});continue
  odd=next((r for r in range(10) if demand[r][r]%2),None)
  if odd is not None:rec['certificates'].append({'assignment':ai,'kind':'odd_internal','support':odd,'count':demand[odd][odd]});continue
  rec['survivors'].append({'assignment':ai,'lows':lows,'demand':demand})
r={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'seconds':r['seconds'],'assignments':sum(len(x['certificates'])+len(x['survivors']) for x in out),'positive_roots':sum(bool(x['survivors']) for x in out),'survivors':sum(len(x['survivors']) for x in out),'asymmetric':sum(z['kind']=='asymmetric' for x in out for z in x['certificates']),'odd':sum(z['kind']=='odd_internal' for x in out for z in x['certificates'])}))
