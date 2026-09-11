from pathlib import Path
import json,itertools,time
root=Path(__file__).parent;start=time.monotonic()
base=json.loads(Path('/tmp/erdos85-sol1-q9-n78-kernel-four-abelian-cayley/parameters.json').read_text())['H_tables'];groups=[]
for H in base:
 for chi in [[0]*8]+H['nonzero_characters']:
  elements=list(itertools.product(range(3),range(8)));ix={g:i for i,g in enumerate(elements)}
  M=[[ix[((c+(-1)**chi[h]*d)%3,H['multiplication'][h][k])] for d,k in elements] for c,h in elements]
  groups.append({'name':H['name']+':'+''.join(map(str,chi)),'elements':elements,'multiplication':M})
perms=list(itertools.permutations(range(4)));ix={x:i for i,x in enumerate(perms)};groups.append({'name':'S4','elements':perms,'multiplication':[[ix[tuple(a[b[i]] for i in range(4))] for b in perms] for a in perms]})
even=[g for g in perms if sum(g[i]>g[j] for i in range(4) for j in range(i+1,4))%2==0];es=list(itertools.product(even,range(2)));ix={g:i for i,g in enumerate(es)};groups.append({'name':'A4xC2','elements':es,'multiplication':[[ix[(tuple(a[b[i]] for i in range(4)),s^t)] for b,t in es] for a,s in es]})
assert len(groups)==24
out=[];expired=False
for gi,group in enumerate(groups):
 if expired:out.append({'group':gi,'status':'UNVISITED'});continue
 M=group['multiplication'];assert all(M[0][a]==M[a][0]==a for a in range(24));inv=[next(b for b in range(24) if M[a][b]==0) for a in range(24)];group['inverse']=inv
 cubic=[];tested=0;actions=[];subgroups=0;status='COMPLETE'
 for S in itertools.combinations(range(1,24),3):
  if time.monotonic()-start>=30:expired=True;status='UNKNOWN';break
  tested+=1;ss=set(S)
  if {inv[a] for a in S}!=ss:continue
  if any(len(ss & {M[g][s] for s in S})>1 for g in range(1,24)):continue
  cubic.append(list(S))
 if not expired and cubic:
  for tail in itertools.combinations(range(1,24),3):
   if time.monotonic()-start>=30:expired=True;status='UNKNOWN';break
   H={0,*tail}
   if any(M[a][b] not in H for a in H for b in H):continue
   subgroups+=1;cosets=[];reps=[];unseen=set(range(24))
   while unseen:
    a=min(unseen);C={M[a][h] for h in H};cosets.append(C);reps.append(a);unseen-=C
   assert len(cosets)==6;labels=[next(i for i,C in enumerate(cosets) if a in C) for a in range(24)]
   for partner,a in enumerate(reps[1:],1):
    if M[a][a] not in H or {M[M[a][h]][inv[a]] for h in H}!=H:continue
    matching=[labels[M[r][a]] for r in reps];assert all(matching[i]!=i and matching[matching[i]]==i for i in range(6))
    actions.append({'H':sorted(H),'coset_representatives':reps,'labels':labels,'partner':partner,'matching':matching})
 out.append({'group':gi,'status':status,'cubic_tested':tested,'cubic_sets':cubic,'subgroups4':subgroups,'actions':actions})
result={'status':'INCOMPLETE' if expired else 'COMPLETE','original_seconds':30,'seconds':time.monotonic()-start,'records':out}
(root/'groups.json').write_text(json.dumps(groups,indent=2)+'\n');(root/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':result['status'],'seconds':result['seconds'],'models':len(groups),'cubic_sets':sum(len(r.get('cubic_sets',[])) for r in out),'actions':sum(len(r.get('actions',[])) for r in out),'surviving':[{'group':r['group'],'name':groups[r['group']]['name'],'cubic':len(r['cubic_sets']),'actions':len(r['actions'])} for r in out if r.get('cubic_sets')]}))
