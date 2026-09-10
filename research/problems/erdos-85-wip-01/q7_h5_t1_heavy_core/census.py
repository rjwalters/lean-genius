"""Bounded H5/T1 heavy-core census and necessary singleton-host matching test."""
import itertools,json,time,functools
from pathlib import Path
start=time.monotonic();LIMIT=100000;SECONDS=60
triple=(0,1,2);pairs=[p for p in itertools.combinations(range(5),2) if not set(p)<=set(triple)]
supports=[triple]+pairs;mask=[sum(1<<c for c in s) for s in supports];n=len(mask);assert n==8
edges=list(itertools.combinations(range(n),2));adj=[0]*n;covered=[0]*n
counts={'nodes':0,'cores':0,'host_pass':0,'host_fail':0};stop=False;orbits={};fails={};hosts=[5,5,5,4,4]
perms=[];by_support={frozenset(s):i for i,s in enumerate(supports)}
for a in itertools.permutations(range(3)):
 for b in itertools.permutations((3,4)):
  perm=a+b;perms.append([by_support[frozenset(perm[c] for c in s)] for s in supports])
def canonical():
 es=[(i,j) for i,j in edges if adj[i]>>j&1]
 return min(tuple(sorted(tuple(sorted((p[i],p[j]))) for i,j in es)) for p in perms)

def host_test(colour):
 needed=[i for i in range(n) if not covered[i]>>colour&1]
 compat={i:sum(1<<j for j in needed if j!=i and not(mask[i]&mask[j]) and not(adj[i]&adj[j])) for i in needed}
 @functools.lru_cache(None)
 def matching(bits):
  if not bits:return 0
  low=bits&-bits;i=low.bit_length()-1;rest=bits^low;best=matching(rest);possible=compat[i]&rest
  while possible:
   bit=possible&-possible;possible^=bit;best=max(best,1+matching(rest^bit))
  return best
 m=matching(sum(1<<i for i in needed));return len(needed)-m<=hosts[colour],len(needed)-m

def visit(k):
 global stop
 if stop:return
 counts['nodes']+=1
 if counts['nodes']%4096==0 and time.monotonic()-start>SECONDS:stop=True;return
 if k==len(edges):
  b=adj[0].bit_count()
  if b not in (1,2):return
  # Pair/pair edges exclude the b triple/pair incidences.
  a=sum(bool(adj[i]>>j&1) for i,j in edges if i>0)
  if min(35-4*a-3*b,5-2*b,b-1,68-4*a-7*b)<0:return
  counts['cores']+=1
  if counts['cores']>LIMIT:stop=True;return
  checks=[host_test(c) for c in range(5)];key=canonical();ok=all(x[0] for x in checks)
  counts['host_pass' if ok else 'host_fail']+=1
  target=orbits if ok else fails
  if key not in target:target[key]={'edges':[list(e) for e in key],'labelled_count':0,'example_minimum_hosts':[x[1] for x in checks],'e22':a,'e23':b}
  target[key]['labelled_count']+=1
  return
 i,j=edges[k]
 visit(k+1)
 if stop:return
 # Neighbour supports partition high colours; also prohibit a second common low neighbour.
 if covered[i]&mask[j] or covered[j]&mask[i]:return
 for x in range(n):
  if (adj[i]>>x&1) and (adj[j]&adj[x]):return
  if (adj[j]>>x&1) and (adj[i]&adj[x]):return
 oldi,oldj=covered[i],covered[j];adj[i]|=1<<j;adj[j]|=1<<i;covered[i]|=mask[j];covered[j]|=mask[i]
 visit(k+1)
 adj[i]^=1<<j;adj[j]^=1<<i;covered[i],covered[j]=oldi,oldj
visit(0)
result={'sector':'H5/T1','supports':supports,'singleton_hosts_by_colour':hosts,'counts':counts,'surviving_orbits':len(orbits),'rejected_orbits':len(fails),'exhaustive_within_stated_core_model':not stop,'caps':{'labelled_cores':LIMIT,'seconds':SECONDS},'seconds':time.monotonic()-start,'survivors':list(orbits.values()),'rejections':list(fails.values()),'scope':'Necessary heavy-core and independent per-colour host feasibility only. Does not assign hosts consistently across colours or complete singleton/empty graph edges. No SAT solver, Lean exclusion, or queue change.'};Path(__file__).with_name('results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['survivors','rejections']}))
