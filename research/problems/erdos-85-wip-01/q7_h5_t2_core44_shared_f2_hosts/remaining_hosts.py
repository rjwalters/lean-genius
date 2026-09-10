"""Necessary per-colour partitions for the 22 remaining singleton vertices."""
import itertools,json,pathlib,time
BASE=pathlib.Path(__file__).parent
def check(adj,deadline,node_cap=100000):
 G=list(map(set,adj));weights=[len(ns&set(range(5))) for ns in G]
 result=[];nodes=0
 def tick():
  nonlocal nodes
  nodes+=1
  if nodes>node_cap or time.monotonic()>deadline:raise TimeoutError
 try:
  for c,cap in enumerate([3,4,3,4,3]):
   req=[v for v in range(5,32) if not G[v]&G[c]]
   groups=[]
   def gen(chosen,tail,w):
    tick()
    if chosen and len(chosen)<=1+w:groups.append(sum(1<<v for v in chosen))
    if len(chosen)==6:return
    for i,v in enumerate(tail):
     if w+weights[v]>5:continue
     gen(chosen+[v],[u for u in tail[i+1:] if not G[u]&G[v]],w+weights[v])
   gen([],req,0)
   by={v:[s for s in groups if s>>v&1] for v in req};failed=set()
   def solve(left,bins):
    tick()
    if not left:return []
    if not bins or (left,bins) in failed:return None
    opts=min(([s for s in by[v] if s&left==s] for v in req if left>>v&1),key=len)
    for s in sorted(opts,key=int.bit_count,reverse=True):
     ans=solve(left^s,bins-1)
     if ans is not None:return [s]+ans
    failed.add((left,bins));return None
   ans=solve(sum(1<<v for v in req),cap)
   result.append(dict(colour=c,required=req,groups=len(groups),capacity=cap,partition=None if ans is None else [[v for v in req if s>>v&1] for s in ans]))
   if ans is None:return dict(status='EXHAUSTED',nodes=nodes,colours=result)
  return dict(status='LOCAL_PARTITIONS',nodes=nodes,colours=result)
 except TimeoutError:return dict(status='CAPPED',nodes=nodes,colours=result)
if __name__=='__main__':
 deadline=time.monotonic()+60;results=[]
 for source in ['core44-special-projection/fstar-empty-results.json','core44-sharing-structure/sharing-empty-results.json']:
  for row in json.loads((BASE.parent/source).read_text())['results']:
   for case in row['choices']:
    if case['status']!='PARTIAL_WITNESS':continue
    result=check(case['adjacency'],deadline)
    result.update(shared=row.get('shared'),omitted=row['omitted'],af=case['af'],bf=case['bf'],internal=case.get('internal',[[1,3]]))
    results.append(result)
    print({k:v for k,v in result.items() if k!='colours'},flush=True)
 (BASE/'remaining-host-results.json').write_text(json.dumps(dict(results=results,scope='Fixed26 partial graphs only; no branch exclusion.'),indent=2)+'\n')
