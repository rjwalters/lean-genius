"""Independent block-matching exhaustion for the five reported T2 rejections."""
import itertools,json,time
from pathlib import Path
C=json.loads(Path('core-t0.json').read_text());masks=C['masks'];n=len(masks);caps=[4+sum(bool(m>>c&1) for m in masks if m.bit_count()==3) for c in range(5)]
supports=masks+[1<<c for c in range(5) for _ in range(caps[c])];N=5+len(supports);S=list(range(5+n,N));col={v:supports[v-5].bit_length()-1 for v in S};deadline=time.monotonic()+60;results=[]
def allowed(G,u,v):
 if u==v or v in G[u]:return False
 return all(not(G[b]&G[w]) for a,b in [(u,v),(v,u)] for w in G[a])
def pmatch(vertices):
 if not vertices:yield ();return
 u=vertices[0]
 for j in range(1,len(vertices)):
  v=vertices[j]
  for rest in pmatch(vertices[1:j]+vertices[j+1:]):yield ((u,v),)+rest
for core in [r['core'] for r in json.loads(Path('singleton-t0.json').read_text())['results'] if r['status']=='EXCLUDED_SINGLETON_COMPLETION']:
 try:
  H=[set() for _ in masks]
  for i,(u,v) in enumerate(itertools.combinations(range(n),2)):
   if core>>i&1:H[u].add(v);H[v].add(u)
  choices=[]
  for c in range(5):
   need=[u for u in range(n) if not any(masks[v]>>c&1 for v in H[u])]
   compat=[p for p in itertools.combinations(need,2) if not(masks[p[0]]&masks[p[1]]) and not(H[p[0]]&H[p[1]])]
   options=[]
   for k in range(max(0,len(need)-caps[c]),len(need)//2+1):
    for pairs in itertools.combinations(compat,k):
     used=[v for p in pairs for v in p]
     if len(set(used))==2*k:options.append(tuple(pairs)+tuple((v,) for v in need if v not in used))
   choices.append(options)
  assignments=nodes=0
  for hosts in itertools.product(*choices):
   pairgroups=[p for groups in hosts for p in groups if len(p)==2]
   if len(set(pairgroups))!=len(pairgroups):continue
   assignments+=1;G=[set() for _ in range(N)]
   def edge(u,v):G[u].add(v);G[v].add(u)
   for v,m in enumerate(supports,5):
    for c in range(5):
     if m>>c&1:edge(c,v)
   for u in range(n):
    for v in H[u]:edge(u+5,v+5)
   offset=5+n
   for c,groups in enumerate(hosts):
    for j,group in enumerate(groups):
     for v in group:edge(offset+j,v+5)
    offset+=caps[c]
   missing={(v,c) for v in S for c in range(5) if not G[v]&G[c]};blocks=[]
   for c in range(5):
    for d in range(c,5):
     left=[v for v in S if col[v]==c and (v,d) in missing];right=[v for v in S if col[v]==d and (v,c) in missing]
     if c==d:
      assert len(left)%2==0;options=list(pmatch(left))
     else:
      assert len(left)==len(right);options=[tuple(zip(left,p)) for p in itertools.permutations(right)]
     options=[o for o in options if all(allowed(G,u,v) for u,v in o)]
     blocks.append(options)
   blocks.sort(key=len)
   def search(depth):
    global nodes
    nodes+=1
    if time.monotonic()>deadline:raise TimeoutError
    if depth==len(blocks):return True
    for option in blocks[depth]:
     added=[]
     for u,v in option:
      if not allowed(G,u,v):break
      edge(u,v);added.append((u,v))
     else:
      if search(depth+1):return True
     for u,v in added:G[u].remove(v);G[v].remove(u)
    return False
   assert not search(0),('unexpected completion',core)
  results.append(dict(core=core,status='INDEPENDENTLY_EXHAUSTED',host_assignments=assignments,nodes=nodes));print(results[-1],flush=True)
 except TimeoutError:
  results.append(dict(core=core,status='VERIFICATION_CAPPED',host_assignments=assignments,nodes=nodes));break
Path('singleton-rejection-audit.json').write_text(json.dumps(results,indent=2)+'\n')
