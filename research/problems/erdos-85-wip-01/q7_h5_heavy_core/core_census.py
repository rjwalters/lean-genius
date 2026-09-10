"""Bounded heavy-support induced core census. No SAT/graph exclusion claim."""
import argparse,itertools,json,time
from pathlib import Path

def census(sector,seconds=60,limit=100000):
 start=time.monotonic();triples=[[],[7],[7,25]][sector]
 pairs=[(1<<a)|(1<<b) for a,b in itertools.combinations(range(5),2) if not any(((1<<a)|(1<<b))&t==((1<<a)|(1<<b)) for t in triples)]
 masks=triples+pairs;n=len(masks);sizes=[x.bit_count() for x in masks]
 edges=list(itertools.combinations(range(n),2));idx={e:i for i,e in enumerate(edges)}
 transforms=[]
 for p in itertools.permutations(range(5)):
  def trans(m):return sum(1<<p[i] for i in range(5) if m>>i&1)
  if sorted(map(trans,triples))!=sorted(triples):continue
  perm=[masks.index(trans(m)) for m in masks]
  transforms.append([1<<idx[tuple(sorted((perm[u],perm[v])))] for u,v in edges])
 adj=[set() for _ in masks];weight=[0]*n;seen=set();labeled=0;nodes=0;hist={};complete=True;stop=None
 def add(u,v):
  if weight[u]+sizes[v]>5 or weight[v]+sizes[u]>5:return False
  if len(adj[u])>=7-sizes[u] or len(adj[v])>=7-sizes[v]:return False
  for a,b in [(u,v),(v,u)]:
   for w in adj[a]:
    if masks[b]&masks[w] or adj[b]&adj[w]:return False
  adj[u].add(v);adj[v].add(u);weight[u]+=sizes[v];weight[v]+=sizes[u];return True
 def remove(u,v):
  adj[u].remove(v);adj[v].remove(u);weight[u]-=sizes[v];weight[v]-=sizes[u]
 def visit(u,bits):
  nonlocal nodes,labeled,complete,stop
  nodes+=1
  if nodes%256==0 and time.monotonic()-start>=seconds:complete=False;stop='time_limit';raise TimeoutError
  if u==n:
   labeled+=1
   active=[i for i in range(len(edges)) if bits>>i&1]
   canon=min(sum(t[i] for i in active) for t in transforms)
   if canon not in seen:
    seen.add(canon);a=b=c=0
    for i in active:
     x,y=edges[i];k=sorted((sizes[x],sizes[y]))
     if k==[2,2]:a+=1
     elif k==[2,3]:b+=1
     else:c+=1
    key=f'{a},{b},{c}';hist[key]=hist.get(key,0)+1
    if len(seen)>=limit:complete=False;stop='normalized_limit';raise TimeoutError
   return
  available=list(range(u+1,n));max_new=min(len(available),(5-weight[u])//2,7-sizes[u]-len(adj[u]))
  for count in range(max_new+1):
   for chosen in itertools.combinations(available,count):
    added=[];nextbits=bits
    for v in chosen:
     if not add(u,v):break
     added.append(v);nextbits|=1<<idx[(u,v)]
    else:
     # Remaining singletons supply exactly the uncovered high colours.
     # Empty-neighbour demand must fit the residual low degree.
     empty=2-sizes[u]+weight[u]-len(adj[u])
     if empty>=0:visit(u+1,nextbits)
    for v in reversed(added):remove(u,v)
 try:visit(0,0)
 except TimeoutError:pass
 return dict(sector=sector,masks=masks,automorphisms=len(transforms),nodes=nodes,labeled=labeled,normalized=len(seen),complete=complete,stop=stop,elapsed_seconds=time.monotonic()-start,edge_ledger_histogram=hist,canonical_cores=sorted(seen),scope='Necessary induced heavy-support cores only; singleton/empty completion not tested')

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--sector',type=int,required=True,choices=range(3));p.add_argument('--seconds',type=float,default=60);p.add_argument('--limit',type=int,default=100000);p.add_argument('--output',required=True);a=p.parse_args()
 result=census(a.sector,a.seconds,a.limit);Path(a.output).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['canonical_cores','edge_ledger_histogram']},indent=2))
