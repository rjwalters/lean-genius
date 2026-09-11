from pathlib import Path
import itertools,json,time
root=Path(__file__).parent;src=Path('/tmp/erdos85-sol1-q9-n78-four-orbit-order24-parameters');Gs=json.loads((src/'groups.json').read_text());Rs=json.loads((src/'results.json').read_text())['records'];start=time.monotonic()
roots=[(r['group'],ai,a) for r in Rs for ai in range(len(r.get('actions',[]))) for a in [1,4]];out=[];expired=False
for ri,(gi,ai,a) in enumerate(roots):
 if expired:out.append({'index':ri,'group':gi,'action':ai,'a':a,'status':'UNVISITED'});continue
 M=Gs[gi]['multiplication'];inv=Gs[gi]['inverse'];action=Rs[gi]['actions'][ai];labels=action['labels'];allowed=set(range(6))-{action['partner']};same=[int(labels[g]==0) for g in range(24)];fibers={f:[g for g in range(24) if labels[g]==f] for f in allowed};internal=[];bylabels={};tvisited=candidates=0;survivors=[];status='COMPLETE'
 def translated(S):return [sum(1<<M[g][s] for s in S) for g in range(24)]
 try:
  for S in itertools.combinations(range(1,24),a):
   if time.monotonic()-start>=30:raise TimeoutError
   ls=frozenset(labels[s] for s in S)
   if len(ls)!=a or not ls<=allowed or {inv[s] for s in S}!=set(S):continue
   tr=translated(S);mask=tr[0];codeg=[(mask&t).bit_count() for t in tr]
   if any(codeg[g]+same[g]>1 for g in range(1,24)):continue
   item={'S':list(S),'labels':ls,'tr':tr,'mask':mask,'codeg':codeg};internal.append(item);bylabels.setdefault(ls,[]).append(item)
  for U in internal:
   missing=sorted(allowed-U['labels'])
   for T in itertools.product(*(fibers[f] for f in missing)):
    if time.monotonic()-start>=30:raise TimeoutError
    tvisited+=1;Ti=[inv[t] for t in T];ls=frozenset(labels[t] for t in Ti)
    if len(ls)!=5-a or not ls<=allowed:continue
    vs=bylabels.get(frozenset(allowed-ls),[])
    if not vs:continue
    tr=translated(T);mask=tr[0]
    if any(U['codeg'][g]+(mask&tr[g]).bit_count()+same[g]>1 for g in range(1,24)):continue
    ti=translated(Ti);mi=ti[0];cg=[(mi&x).bit_count() for x in ti]
    for V in vs:
     candidates+=1
     if any(V['codeg'][g]+cg[g]+same[g]>1 for g in range(1,24)):continue
     if any((U['mask']&ti[g]).bit_count()+(mask&V['tr'][g]).bit_count()+same[g]>1 for g in range(24)):continue
     survivors.append({'U':U['S'],'V':V['S'],'T':list(T)})
 except TimeoutError:expired=True;status='UNKNOWN'
 out.append({'index':ri,'group':gi,'action':ai,'a':a,'status':status,'internal_sets':len(internal),'cross_choices_visited':tvisited,'coupled_candidates':candidates,'survivors':survivors})
result={'status':'INCOMPLETE' if expired else 'COMPLETE','original_seconds':30,'seconds':time.monotonic()-start,'records':out};(root/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':result['status'],'seconds':result['seconds'],'roots':len(out),'states':{s:sum(r['status']==s for r in out) for s in ['COMPLETE','UNKNOWN','UNVISITED']},'surviving_roots':sum(bool(r.get('survivors')) for r in out),'survivors':sum(len(r.get('survivors',[])) for r in out),'cross_choices':sum(r.get('cross_choices_visited',0) for r in out),'coupled_candidates':sum(r.get('coupled_candidates',0) for r in out)}))
