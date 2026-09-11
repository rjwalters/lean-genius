from pathlib import Path
import json,itertools as it,time,functools
p=Path(__file__).resolve().parent;b=p.parent;start=time.monotonic();data=json.loads((b/'residual-ten-D5-five-311-full-center-configurations/results.json').read_text())['records'];high={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-high-center-assignments/results.json').read_text())['records']};cross={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-center-cross-domains/results.json').read_text())['records']};original={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-center-domains/results.json').read_text())['records']};prop={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-low-propagation/results.json').read_text())['records']};edgecases={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-low-edge-capacity/results.json').read_text())['records']};joint={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-nonempty-joint/results.json').read_text())['records']};graphs={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-high-matchings/results.json').read_text())['records']};pack=json.loads((b/'residual-ten-D5-five-311-packing/results.json').read_text())['records'];dom=json.loads((b/'residual-ten-D5-supports/results.json').read_text())['records'];out=[]
def guard():
 if time.monotonic()-start>=30:raise TimeoutError
try:
 for entry in data:
  guard();o=original[entry['root']];src=o['source_root'];ai=o['source_assignment'];lows=next(a['lows'] for a in edgecases[src]['survivors'] if a['assignment']==ai);a=next(a for a in prop[src]['survivors'] if a['assignment']==ai);source=joint[src];ci=source['class'];root=pack[ci]['survivors'][source['source_root']];c=dom[ci];ss=[c['high3'][j] for j in root['high3']];S=[set(t) for s in ss for t in (s,[e^1 for e in s])];rho={v:w for v,w in c['edges']}|{w:v for v,w in c['edges']};Hg=graphs[source['packing_root']]['survivors'][source['graph']]['edges'];cd=cross[entry['root']];rec={'root':entry['root'],'status':'UNKNOWN','records':[]};out.append(rec)
  for hc in entry['configs']:
   h=high[entry['root']]['survivors'][hc['high_assignment']]
   for ki,cfg in enumerate(hc['survivors']):
    guard();colors=[-1]*50
    for f,j in enumerate(h['high_options']):
     for oi in cd['high_groups'][f][j]:
      for v in o['low_orbits'][oi]:colors[v]=f
    for j,li in enumerate(cfg['low_options']):
     for oi in cd['low_groups'][li]['orbits']:
      for v in o['low_orbits'][oi]:colors[v]=5+j
    assert min(colors)>=0;N=[set() for _ in range(80)];chosen=[set() for _ in lows];candidate=[set() for _ in lows];trace=[]
    def edge(v,w):N[v].add(w);N[w].add(v)
    def remove(v,w):candidate[v].discard(w);candidate[w].discard(v)
    for v,w in c['edges']:edge(v,w)
    for v,s in enumerate(S):
     for r in s:edge(10+v,r)
     edge(10+v,70+v//2)
    for v,w in Hg:edge(10+v,10+w)
    for i,(v,r) in enumerate(lows):
     edge(20+i,r);edge(20+i,70+colors[i])
     if v>=0:edge(20+i,10+v)
    for v,w in cfg['center_edges']:edge(70+v,70+w)
    for i,j in a['forced_edges']:edge(20+i,20+j);chosen[i].add(j);chosen[j].add(i)
    for i,j in a['remaining_edges']:candidate[i].add(j);candidate[j].add(i)
    goals=[6 if v>=0 else 7 for v,r in lows];rtarget=[set(range(10))-({rho[r]}|(S[v] if v>=0 else set())) for v,r in lows];ctarget=[set(range(10))-{v-70 for v in N[70+colors[i]] if v>=70}-({v//2} if v>=0 else set()) for i,(v,r) in enumerate(lows)];assert all(len(t)==g for t,g in zip(ctarget,goals));masks=[sum(1<<v for v in ns) for ns in N];bad=None
    pair=next(((i,j) for i,j in it.combinations(range(80),2) if (masks[i]&masks[j]).bit_count()>1),None)
    if pair:bad={'kind':'base_C4','pair':pair,'common':sorted(N[pair[0]]&N[pair[1]])}
    while bad is None:
     guard();removed=[]
     for i in range(50):
      usedR={lows[j][1] for j in chosen[i]};usedC={colors[j] for j in chosen[i]}
      for j in sorted(candidate[i]):
       if lows[j][1] not in rtarget[i] or colors[j] not in ctarget[i] or lows[j][1] in usedR or colors[j] in usedC or len(chosen[i])==goals[i]:remove(i,j);removed.append([i,j,'slot'])
     masks=[sum(1<<v for v in ns) for ns in N]
     for i in range(50):
      for j in sorted(candidate[i]):
       if i<j and (any(masks[20+i]&masks[z] for z in N[20+j]) or any(masks[20+j]&masks[z] for z in N[20+i])):remove(i,j);removed.append([i,j,'C4'])
     if removed:trace.append({'removed':removed})
     force=None
     for i,(v,r) in enumerate(lows):
      usedR={lows[j][1] for j in chosen[i]};usedC={colors[j] for j in chosen[i]};slots=goals[i]-len(chosen[i]);byR={e:[j for j in sorted(candidate[i]) if lows[j][1]==e] for e in sorted({lows[j][1] for j in candidate[i]})};byC={e:[j for j in sorted(candidate[i]) if colors[j]==e] for e in sorted({colors[j] for j in candidate[i]})}
      if slots<0 or len(usedR)!=len(chosen[i]) or len(usedC)!=len(chosen[i]) or len(byR)<slots or not ctarget[i]-usedC<=set(byC) or (v>=0 and not rtarget[i]-usedR<=set(byR)):
       bad={'kind':'slot_shortage','low':i,'slots':slots,'usedR':sorted(usedR),'usedC':sorted(usedC),'availableR':sorted(byR),'availableC':sorted(byC)};break
      requiredR=rtarget[i]-usedR if v>=0 else set(byR) if len(byR)==slots else set()
      singleton=next(((ds[0],label,e) for label,by,req in [('center',byC,ctarget[i]-usedC),('residual',byR,requiredR)] for e in sorted(req) for ds in [by[e]] if len(ds)==1),None)
      if singleton:force=(i,singleton[0],{'kind':'required_singleton','type':singleton[1],'target':singleton[2]});break
      centers=sorted(ctarget[i]-usedC)
      @functools.lru_cache(None)
      def hall(k,used):
       if k==len(centers):return True
       return any(not used>>lows[j][1]&1 and hall(k+1,used|1<<lows[j][1]) for j in byC[centers[k]])
      if not hall(0,0):bad={'kind':'local_Hall','low':i,'center_support_domains':[[g,sorted({lows[j][1] for j in byC[g]})] for g in centers]};break
     if bad or force is None:break
     i,j,reason=force;trace.append({'forced':[i,j],'reason':reason});remove(i,j);chosen[i].add(j);chosen[j].add(i);edge(20+i,20+j)
    result={'high_assignment':hc['high_assignment'],'center_config':ki,'status':'NEGATIVE' if bad else 'SURVIVES','trace':trace,'forced_edges':[[i,j] for i in range(50) for j in sorted(chosen[i]) if i<j]}
    if bad:result['certificate']=bad
    else:result['remaining_edges']=[[i,j] for i in range(50) for j in sorted(candidate[i]) if i<j]
    rec['records'].append(result)
  rec['status']='COMPLETE'
 status='COMPLETE'
except TimeoutError:status='INCOMPLETE'
seen={r['root'] for r in out}
for entry in data:
 if entry['root'] not in seen:out.append({'root':entry['root'],'status':'UNVISITED'})
r={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':status,'seconds':r['seconds'],'complete_cases':sum(r['status']=='COMPLETE' for r in out),'processed_configs':sum(len(r.get('records',[])) for r in out),'positive_configs':sum(x['status']=='SURVIVES' for r in out for x in r.get('records',[])),'positive_cases':sum(any(x['status']=='SURVIVES' for x in r.get('records',[])) for r in out)}))
