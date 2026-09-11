from pathlib import Path
import itertools,json,time
out=Path(__file__).parent
ps=list(itertools.permutations(range(4)));ix={p:i for i,p in enumerate(ps)}
def compose(a,b):return tuple(a[b[i]] for i in range(4))
pm=[[ix[compose(a,b)] for b in ps] for a in ps];pinv=[next(j for j in range(24) if pm[i][j]==pm[j][i]==0) for i in range(24)]
r=ix[(1,2,3,0)];H={0};cur=0
for _ in range(3):cur=pm[cur][r];H.add(cur)
assert len(H)==4
N={g for g in range(24) if {pm[pm[g][h]][pinv[g]] for h in H}==H};assert len(N)==8
partner={pm[min(N-H)][h] for h in H};allcosets={frozenset(pm[g][h] for h in H) for g in range(24)};assert len(allcosets)==6
cosets=[frozenset(H),frozenset(partner)]+sorted(allcosets-{frozenset(H),frozenset(partner)},key=lambda c:min(c));labels=[next(i for i,c in enumerate(cosets) if g//2 in c) for g in range(48)]
mul=[[2*pm[a//2][b//2]+((a%2)^(b%2)) for b in range(48)] for a in range(48)];inv=[2*pinv[a//2]+a%2 for a in range(48)]
fibers=[[a for a in range(1,48) if labels[a]==i] for i in [0,2,3,4,5]];assert list(map(len,fibers))==[7,8,8,8,8]
start=time.monotonic();raw=closed=0;certs=[];survivors=[];state='COMPLETE'
for choice in itertools.product(*fibers):
 if time.monotonic()-start>30:state='UNKNOWN_CAP';break
 raw+=1;S=set(choice)
 if {inv[a] for a in S}!=S:continue
 closed+=1
 for g in range(1,48):
  common=sorted(S&{mul[g][s] for s in S})
  if len(common)+int(labels[g]==0)>1:
   if labels[g]==0:cycle=[6,6+common[0],6+g,0]
   else:cycle=[6,6+common[0],6+g,6+common[1]]
   assert len(set(cycle))==4
   certs.append({'S':sorted(S),'g':g,'common':common,'shared_center':labels[g]==0,'cycle':cycle});break
 else:survivors.append(sorted(S))
result={'status':state,'original_cap_seconds':30,'seconds':time.monotonic()-start,'raw':raw,'inverse_closed':closed,'obstructions':len(certs),'survivors':survivors}
(out/'results.json').write_text(json.dumps(result,indent=2)+'\n');(out/'certificates.json').write_text(json.dumps(certs,indent=2)+'\n');(out/'group.json').write_text(json.dumps({'permutations':ps,'multiplication':mul,'inverse':inv,'C4':sorted(H),'normalizer':sorted(N),'cosets':[sorted(c) for c in cosets],'center_labels':labels},indent=2)+'\n');print(json.dumps(result))
