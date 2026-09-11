from pathlib import Path
import json,itertools as it,time
p=Path(__file__).resolve().parent;b=p.parent;start=time.monotonic();data=json.loads((b/'residual-ten-D5-five-311-low-edge-capacity/results.json').read_text())['records'];joint={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-nonempty-joint/results.json').read_text())['records']};graphs={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-high-matchings/results.json').read_text())['records']};pack=json.loads((b/'residual-ten-D5-five-311-packing/results.json').read_text())['records'];dom=json.loads((b/'residual-ten-D5-supports/results.json').read_text())['records'];out=[]
def guard():
 if time.monotonic()-start>=30:raise TimeoutError
for entry in data:
 source=joint[entry['root']];ci=source['class'];root=pack[ci]['survivors'][source['source_root']];c=dom[ci];ss=[c['high3'][j] for j in root['high3']];S=[set(t) for s in ss for t in (s,[e^1 for e in s])];rho={v:w for a,z in c['edges'] for v,w in [(a,z),(z,a)]};Hg=graphs[source['packing_root']]['survivors'][source['graph']]['edges'];rec={'root':entry['root'],'certificates':[],'survivors':[]};out.append(rec)
 for a in entry['survivors']:
  guard();lows=a['lows'];N=[set() for _ in range(70)];candidate=[set() for _ in lows];chosen=[set() for _ in lows];trace=[]
  def edge(v,w):N[v].add(w);N[w].add(v)
  def remove(i,j):candidate[i].discard(j);candidate[j].discard(i)
  for v,w in c['edges']:edge(v,w)
  for v,s in enumerate(S):
   for r in s:edge(10+v,r)
  for v,w in Hg:edge(10+v,10+w)
  for i,(v,r) in enumerate(lows):
   edge(20+i,r)
   if v>=0:edge(20+i,10+v)
  for i,j in a['allowed_edges']:candidate[i].add(j);candidate[j].add(i)
  goals=[6 if v>=0 else 7 for v,r in lows];targets=[set(range(10))-({rho[r]}|(S[v] if v>=0 else set())) for v,r in lows];bad=None
  while True:
   guard();removed=[]
   for i in range(50):
    used={lows[j][1] for j in chosen[i]}
    for j in sorted(candidate[i]):
     if lows[j][1] in used or len(chosen[i])==goals[i]:remove(i,j);removed.append([i,j,'support_or_degree'])
   masks=[sum(1<<z for z in ns) for ns in N]
   for i in range(50):
    for j in sorted(candidate[i]):
     if j<i:continue
     x,y=20+i,20+j
     if any(masks[x]&masks[z] for z in N[y]) or any(masks[y]&masks[z] for z in N[x]):remove(i,j);removed.append([i,j,'C4'])
   if removed:trace.append({'removed':removed})
   forced=None
   for i,(v,r) in enumerate(lows):
    used={lows[j][1] for j in chosen[i]};slots=goals[i]-len(chosen[i]);by={e:[j for j in sorted(candidate[i]) if lows[j][1]==e] for e in sorted({lows[j][1] for j in candidate[i]})}
    if slots<0 or len(used)!=len(chosen[i]) or len(by)<slots or (v>=0 and not targets[i]-used<=set(by)):
     bad={'kind':'support_shortage','low':i,'slots':slots,'used':sorted(used),'remaining_supports':sorted(by)};break
    required=targets[i]-used if v>=0 else set(by) if len(by)==slots else set()
    one=next((e for e in sorted(required) if len(by[e])==1),None)
    if one is not None:forced=(i,by[one][0],{'kind':'required_singleton','support':one,'slots':slots,'available_supports':len(by)});break
    if slots>0 and len(candidate[i])==slots:forced=(i,min(candidate[i]),{'kind':'all_remaining_edges','slots':slots});break
   if bad:break
   if forced is None:break
   i,j,reason=forced;trace.append({'forced':[i,j],'reason':reason});remove(i,j);chosen[i].add(j);chosen[j].add(i);edge(20+i,20+j)
  result={'assignment':a['assignment'],'trace':trace,'forced_edges':[[i,j] for i in range(50) for j in sorted(chosen[i]) if i<j]}
  if bad:rec['certificates'].append({**result,**bad})
  else:rec['survivors'].append({**result,'remaining_edges':[[i,j] for i in range(50) for j in sorted(candidate[i]) if i<j]})
r={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'seconds':r['seconds'],'negative':sum(len(r['certificates']) for r in out),'assignments':sum(len(r['survivors']) for r in out),'positive_cases':sum(bool(r['survivors']) for r in out),'forced_total':sum(len(a['forced_edges']) for r in out for a in r['certificates']+r['survivors'])}))
