"""Local nonempty-neighbour completion necessity for fixed H7 partials."""
from pathlib import Path
import json,itertools,hashlib,time
p=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01/q7_h7_labelled_incidence/pilot-1.json');raw=p.read_bytes();start=time.monotonic();out=[]
for row in json.loads(raw)['results']:
 if not row['witness']:continue
 g=[set() for _ in range(49)]
 for a,b in row['witness']['partial_edges']:g[a].add(b);g[b].add(a)
 nonempty=[v for v in range(7,49) if g[v]&set(range(7))];assert nonempty==list(range(14,49))
 support={v:g[v]&set(range(7)) for v in nonempty};checks=[]
 for v in nonempty:
  degree=7-len(g[v]);candidates=[w for w in nonempty if w!=v and w not in g[v] and not any(g[w]&g[x] for x in g[v])];nodes=0
  def search(left,chosen):
   global nodes
   nodes+=1
   if not left:return chosen if len(chosen)==degree else None
   if len(chosen)>=degree or len(left)<degree-len(chosen) or len(left)>2*(degree-len(chosen)):return None
   c=min(left)
   for w in candidates:
    if c in support[w] and support[w]<=left and all(not(g[w]&g[x]) for x in chosen):
     r=search(left-support[w],chosen+[w])
     if r is not None:return r
   return None
  answer=search(set(range(7)),[])
  checks.append({'vertex':v,'residual_degree':degree,'candidate_count':len(candidates),'nodes':nodes,'status':'PASS_LOCAL' if answer is not None else 'FAIL_LOCAL','one_neighbour_set':answer})
 out.append({'empty_mask':row['mask'],'failures':[r['vertex'] for r in checks if r['status']=='FAIL_LOCAL'],'checks':checks})
result={'input_sha256':hashlib.sha256(raw).hexdigest(),'seconds':time.monotonic()-start,'scope':'Only26 fixed saved incidence witnesses, no alternate assignments and no capped case retried. Each vertex checked independently; success is not mutual graph feasibility.','fixed_partials':len(out),'fixed_partials_failing':sum(bool(r['failures']) for r in out),'rows':out};Path(__file__).with_name('results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='rows'}))
