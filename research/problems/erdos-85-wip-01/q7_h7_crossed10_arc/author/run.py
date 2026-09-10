import pathlib,json,time,collections,gzip
from arc_filter import check
from local_filter import check_host_assignment
P=pathlib.Path(__file__).parent
source=json.loads((P/'profile-source.json').read_text());profile=next(r for r in source['results'] if not r['twins_adjacent'] and r['profile_index']==10)
assert profile['status']=='COMPLETE' and len(profile['assignments'])==1647
sd=json.loads((P/'seed-source.json').read_text());seed=next(r['adjacency'] for r in sd['patterns'] if not r['twins_adjacent']);idx={n:i for i,n in enumerate(sd['names'])};H=sorted(seed[0]);out=[];start=time.monotonic();deadline=start+60
for i,assignment in enumerate(profile['assignments']):
 if time.monotonic()>deadline:break
 g=list(map(set,seed))
 def add(u,v):g[u].add(v);g[v].add(u)
 for h,m in zip(H,assignment):
  for e,(a,b) in enumerate(profile['edge_order']):
   if m>>e&1:add(h,idx[f'P{a}{b}'])
 for c in range(1,7):
  holes=[h for h in H if not g[h]&g[c]];assert len(holes)==2
  for letter,h in zip('ab',holes):add(h,idx[f'S{c}{letter}'])
 e=0
 for h in H:
  for _ in range(7-len(g[h])):add(h,idx[f'E{e}']);e+=1
 assert e==7
 adjacency=[sorted(ns) for ns in g]
 local=check_host_assignment(adjacency,max_nodes=100000,deadline=deadline)
 if local['status']=='LOCAL_FEASIBLE':
  result=check(adjacency,max_nodes=max(0,100000-local['nodes']),deadline=deadline);result['local_nodes']=local['nodes'];result['nodes']+=local['nodes']
 else:result=dict(status='INFEASIBLE_LOCAL' if local['status']=='INFEASIBLE' else 'UNKNOWN',nodes=local['nodes'],local_result=local)
 result['assignment_index']=i;result['adjacency']=adjacency;out.append(result)
 if len(out)%200==0:print(len(out),dict(collections.Counter(r['status'] for r in out)),round(time.monotonic()-start,2),flush=True)
summary=dict(total=1647,visited=len(out),unvisited=1647-len(out),counts=dict(collections.Counter(r['status'] for r in out)),nodes=sum(r['nodes'] for r in out),seconds=time.monotonic()-start,scope='Single new crossed10 pass;100k combined local/generation/AC operations perassignment60s overall. UNKNOWN/unvisited not excluded. No retries.')
with gzip.open(P/'results.json.gz','wt') as f:json.dump(dict(summary=summary,results=out),f)
(P/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(summary,flush=True)
