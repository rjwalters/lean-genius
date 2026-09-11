from pathlib import Path
import json,itertools,time
p=Path(__file__).parent;src=Path('/tmp/erdos85-sol1-q9-n78-kernel-eight-cayley-examples/results.json');data=json.loads(src.read_text());start=time.monotonic();out=[]
for group in data['groups']:
 G=group['group'];mul=group['multiplication'];sets=[v['S'] for v in group['survivors']];n=len(sets);tested=0;survivors=[];status='COMPLETE'
 internal=[[sum(1<<mul[g][s] for s in S) for g in range(24)] for S in sets]
 crosschoices=list(itertools.product([i for i,g in enumerate(G) if g[-1]==1],[i for i,g in enumerate(G) if g[-1]==2]))
 for ai,bi in itertools.product(range(n),repeat=2):
  if status!='COMPLETE':break
  for T in crosschoices:
   if time.monotonic()-start>=30:status='UNKNOWN';break
   adj=internal[ai].copy()+[x<<24 for x in internal[bi]]
   for g in range(24):
    for t in T:
     h=mul[g][t];adj[g]|=1<<(24+h);adj[24+h]|=1<<g
   tested+=1
   ok=True
   for i in range(48):
    for j in range(i):
     samecenter=(i//24==j//24 and G[i%24][-1]==G[j%24][-1])
     if (adj[i]&adj[j]).bit_count()+samecenter>1:ok=False;break
    if not ok:break
   if ok:survivors.append({'left':ai,'right':bi,'cross':T})
 out.append({'name':group['name'],'status':status,'tested':tested,'total':n*n*64,'survivors':survivors,'remaining':n*n*64-tested})
 (p/'results.json').write_text(json.dumps({'original_seconds':30,'seconds':time.monotonic()-start,'groups':out},indent=2)+'\n')
 print(group['name'],status,tested,len(survivors),flush=True)
