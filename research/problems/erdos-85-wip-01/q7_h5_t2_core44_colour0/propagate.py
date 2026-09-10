"""Deterministic degree/colour propagation on fully labelled partial graphs."""
import pathlib,json,time
P=pathlib.Path(__file__).parent
def bits(n):
 while n:
  b=n&-n;yield b.bit_length()-1;n-=b
def propagate(adjacency,deadline):
 g=[sum(1<<v for v in ns) for ns in adjacency];mask=[x&31 for x in g];added=[]
 while True:
  if time.monotonic()>deadline:return dict(status='WALL_LIMIT',added=added)
  degree=[x.bit_count() for x in g];missing=[]
  for u in range(49):
   covered=0
   for v in bits(g[u]&~31):covered|=mask[v]
   missing.append(31^covered)
  active=sum(1<<u for u in range(5,49) if degree[u]<7)
  if not active:
   assert all(missing[u]==0 for u in range(5,49))
   return dict(status='COMPLETE',added=added,adjacency=[list(bits(x)) for x in g])
  for u in range(5,49):
   if degree[u]>7 or (degree[u]==7 and missing[u]):return dict(status='REJECTED',added=added,reason=['degree_colour',u])
  domains={};force=None
  for u in bits(active):
   two=0
   for w in bits(g[u]):two|=g[w]
   forbidden=0
   for w in bits(two):forbidden|=g[w]
   available=active&~forbidden&~(1<<u)
   opts=0
   for v in bits(available):
    if mask[v]&missing[u]==mask[v] and mask[u]&missing[v]==mask[u]:opts|=1<<v
   domains[u]=opts
   if opts.bit_count()<7-degree[u]:return dict(status='REJECTED',added=added,reason=['degree_capacity',u])
   for c in bits(missing[u]):
    targets=sum(1<<v for v in bits(opts) if mask[v]>>c&1)
    if not targets:return dict(status='REJECTED',added=added,reason=['colour_capacity',u,c])
    if targets.bit_count()==1:force=(u,next(bits(targets)));break
   if force:break
   if opts.bit_count()==7-degree[u]:force=(u,next(bits(opts)));break
  if force:
   u,v=force
   assert v not in bits(g[u]) and all(not g[v]&g[w] for w in bits(g[u]))
   g[u]|=1<<v;g[v]|=1<<u;added.append([u,v]);continue
  return dict(status='UNRESOLVED',added=added,adjacency=[list(bits(x)) for x in g],domain_sizes={u:x.bit_count() for u,x in domains.items()})
if __name__=='__main__':
 deadline=time.monotonic()+60;empty=json.loads((P/'empty-slot-results.json').read_text())['results'];results=[]
 for bi,row in enumerate(json.loads((P/'heavy-slot-results.json').read_text())['results']):
  counts={};cases=[]
  for hi,h in enumerate(row['survivors']):
   g=list(map(set,empty[bi]['survivors'][h['empty_index']]['adjacency']))
   for u,v in h['edges']:g[u].add(v);g[v].add(u)
   result=propagate(g,deadline);result['heavy_index']=hi;cases.append(result);counts[result['status']]=counts.get(result['status'],0)+1
   if result['status']=='WALL_LIMIT':break
  results.append(dict(omitted=row['omitted'],internal=row['internal'],counts=counts,cases=cases,unvisited=len(row['survivors'])-len(cases)))
  print(row['omitted'],row['internal'],counts,flush=True)
 (P/'propagation-results.json').write_text(json.dumps(dict(results=results,scope='Deterministic forcing on conditional colour0/heavy domain; no branching search.'),indent=2)+'\n')
