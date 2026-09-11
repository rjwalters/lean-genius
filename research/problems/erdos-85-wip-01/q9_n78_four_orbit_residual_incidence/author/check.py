from pathlib import Path
import json,time
p=Path(__file__).parent;src=Path('/tmp/erdos85-sol1-q9-n78-four-orbit-order24-parameters');Gs=json.loads((src/'groups.json').read_text());As=json.loads((src/'results.json').read_text())['records'];Ws=json.loads(Path('/tmp/erdos85-sol1-q9-n78-four-orbit-cross/witnesses.json').read_text());start=time.monotonic();out=[];expired=False
for index,w in enumerate(Ws):
 if expired:out.append({'index':index,'status':'UNVISITED'});continue
 M=Gs[w['group']]['multiplication'];labels=As[w['group']]['actions'][w['action']]['labels'];N=[set(row) for row in w['neighbors']];compatible=[sum(1<<j for j in range(48) if j!=i and not(N[6+i]&N[6+j])) for i in range(48)];ds=[sum(1<<j for j in range(48) if labels[j%24]==f)&compatible[0] for f in range(1,6)];nodes=[0];leaves=[0]
 def dfs(domains,chosen,left):
  nodes[0]+=1
  if time.monotonic()-start>=30:raise TimeoutError
  if left>3 or left+len(domains)<3:return None
  if not domains:
   leaves[0]+=1;B=set(chosen)
   if any(len(B & {24*(b//24)+M[g][b%24] for b in chosen})>1 for g in range(1,24)):return None
   return chosen
  domains=sorted(domains,key=int.bit_count);mask=domains[0]
  while mask:
   bit=mask&-mask;mask-=bit;v=bit.bit_length()-1
   answer=dfs([d&compatible[v] for d in domains[1:]],chosen+[v],left+int(v<24))
   if answer is not None:return answer
  return None
 try:
  answer=dfs(ds,[0],1);out.append({'index':index,'source_root':w['root'],'source_configuration':w['configuration'],'status':'WITNESS' if answer else 'INFEASIBLE','nodes':nodes[0],'transversals':leaves[0],'witness':answer})
 except TimeoutError:expired=True;out.append({'index':index,'status':'UNKNOWN','nodes':nodes[0]})
result={'status':'INCOMPLETE' if expired else 'COMPLETE','original_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':result['status'],'seconds':result['seconds'],'states':{s:sum(r['status']==s for r in out) for s in ['WITNESS','INFEASIBLE','UNKNOWN','UNVISITED']},'nodes':sum(r.get('nodes',0) for r in out),'transversals':sum(r.get('transversals',0) for r in out)}))
