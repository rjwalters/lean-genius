"""Singleton-host feasibility for H5 heavy cores; no remaining-edge completion."""
import argparse,itertools,json,time,hashlib
from pathlib import Path

def hostings(required,masks,adj,capacity):
 out=[]
 def visit(left,groups):
  if len(groups)+(len(left)+1)//2>capacity:return
  if not left:
   out.append(tuple(groups));return
  u=left[0];tail=left[1:]
  visit(tail,groups+[(u,)])
  for j,v in enumerate(tail):
   if not(masks[u]&masks[v]) and not(adj[u]&adj[v]):
    visit(tail[:j]+tail[j+1:],groups+[(u,v)])
 visit(tuple(required),[])
 return out

def solve(core,masks,sector,cap,deadline):
 n=len(masks);adj=[set() for _ in masks]
 for i,(u,v) in enumerate(itertools.combinations(range(n),2)):
  if core>>i&1:adj[u].add(v);adj[v].add(u)
 triples=[m for m in masks if m.bit_count()==3]
 capacities=[4+sum(bool(m>>c&1) for m in triples) for c in range(5)]
 options=[]
 for c in range(5):
  required=[u for u in range(n) if not any(masks[v]>>c&1 for v in adj[u])]
  groups=hostings(required,masks,adj,capacities[c]);options.append(groups)
 counts=list(map(len,options))
 if not all(counts):return dict(core=core,status='EXCLUDED_HOST_CAPACITY',options=counts,nodes=0)
 order=sorted(range(5),key=lambda c:len(options[c]));chosen=[None]*5;nodes=0
 def search(depth,used):
  nonlocal nodes
  nodes+=1
  if nodes>cap or time.monotonic()>deadline:raise TimeoutError
  if depth==5:return True
  colour=order[depth]
  for groups in options[colour]:
   pairs={group for group in groups if len(group)==2}
   if pairs&used:continue
   chosen[colour]=groups
   if search(depth+1,used|pairs):return True
  return False
 try:found=search(0,set())
 except TimeoutError:return dict(core=core,status='CAPPED',options=counts,nodes=nodes)
 return dict(core=core,status='PARTIAL_WITNESS' if found else 'EXCLUDED_JOINT_HOSTS',options=counts,nodes=nodes,hosts=chosen if found else None)

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--sector',type=int,choices=[0,2],required=True);parser.add_argument('--seconds',type=float,default=60);parser.add_argument('--nodes',type=int,default=100000);parser.add_argument('--output',required=True);a=parser.parse_args()
 path=Path(f'core-t{a.sector}.json');raw=path.read_bytes();source=json.loads(raw);assert source['complete']
 start=time.monotonic();deadline=start+a.seconds;results=[]
 for core in source['canonical_cores']:
  if time.monotonic()>deadline:break
  results.append(solve(core,source['masks'],a.sector,a.nodes,deadline))
 counts={s:sum(r['status']==s for r in results) for s in sorted({r['status'] for r in results})}
 result=dict(sector=a.sector,source_sha256=hashlib.sha256(raw).hexdigest(),source_count=source['normalized'],visited=len(results),unvisited=source['normalized']-len(results),counts=counts,seconds=time.monotonic()-start,node_cap=a.nodes,wall_cap_seconds=a.seconds,results=results,scope='Singleton-host necessity/partial witnesses only; singleton-singleton, heavy-empty and remaining edges not completed')
 Path(a.output).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='results'},indent=2))
if __name__=='__main__':main()
