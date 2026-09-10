import pathlib,json,itertools,time,hashlib,math
P=pathlib.Path('/Users/rwalters/lean-genius-q7-outside-first-20260910/core44-colour0-structure');O=pathlib.Path(__file__).parent
pins=json.loads((P/'completion-pins.json').read_text())
assert all(hashlib.sha256((P/f).read_bytes()).hexdigest()==h for f,h in pins.items())
rows=json.loads((P/'skeletons.json').read_text())['results'];start=time.monotonic();out=[];nodes=0

def bits(n):
 while n:
  b=n&-n;yield b.bit_length()-1;n-=b

def tick():
 global nodes
 nodes+=1
 if nodes>100000 or time.monotonic()-start>60:raise TimeoutError

def add(g,u,v):g[u]|=1<<v;g[v]|=1<<u

def clean(g):return all((g[u]&g[v]).bit_count()<=1 for u,v in itertools.combinations(range(49),2))

def cover(g,u):
 m=0
 for v in bits(g[u]&~31):m|=g[v]&31
 return m

def legal(g,u,v):
 if u==v or g[u]>>v&1 or g[u].bit_count()>=7 or g[v].bit_count()>=7:return False
 if (g[v]&31)&cover(g,u) or (g[u]&31)&cover(g,v):return False
 return all(not (g[v]&g[w]) for w in bits(g[u]))

def solve(g):
 tick()
 while True:
  domains={};forced=None
  for u in range(48,4,-1):
   d=g[u].bit_count();miss=31^cover(g,u)
   if d>7 or (d==7 and miss):return False
   if d==7:continue
   opts=[v for v in range(48,4,-1) if legal(g,u,v)]
   if len(opts)<7-d:return False
   domains[u]=opts
   for c in bits(miss):
    a=[v for v in opts if g[v]>>c&1]
    if not a:return False
    if len(a)==1:forced=(u,a[0]);break
   if forced:break
   if len(opts)==7-d:forced=(u,opts[-1]);break
  if forced:add(g,*forced);tick();continue
  if not domains:
   assert clean(g)
   return True
  # Whole degree row, not author's missing-colour single-edge branch.
  u=min(domains,key=lambda u:(math.comb(len(domains[u]),7-g[u].bit_count()),-u))
  for block in itertools.combinations(domains[u],7-g[u].bit_count()):
   q=g.copy();valid=True
   for v in block:
    if not legal(q,u,v):valid=False;break
    add(q,u,v)
   if valid and solve(q):return True
  return False

for row in rows:
 counts={'empty_assignments':0,'empty_survivors':0,'heavy_leaves':0,'solutions':0};begin=nodes
 base=[sum(1<<v for v in ns) for ns in row['adjacency']];assert clean(base)
 vacant=[e for e in range(11,23) if not base[e]&base[0]];assert len(vacant)==5
 def heavy(g,k):
  tick()
  requests=[(9,4),(9,3),(8,4),(8,3),(7,1)]
  if k==5:
   counts['heavy_leaves']+=1
   if solve(g.copy()):counts['solutions']+=1
   return
  h,c=requests[k]
  for v in range(48,34,-1):
   if g[v]&31!=1<<c or not legal(g,h,v):continue
   q=g.copy();add(q,h,v);heavy(q,k+1)
 try:
  for pair in itertools.combinations(vacant,2):
   for triple in itertools.permutations([e for e in vacant if e not in pair]):
    counts['empty_assignments']+=1;g=base.copy()
    for h,es in [(27,pair),(32,[triple[0]]),(33,[triple[1]]),(34,[triple[2]])]:
     for e in es:add(g,h,e)
    if not clean(g):continue
    counts['empty_survivors']+=1;heavy(g,0)
  status='EXHAUSTED' if counts['solutions']==0 else 'FOUND'
 except TimeoutError:status='UNKNOWN'
 result={'omitted':row['omitted'],'internal':row['internal'],'status':status,'nodes':nodes-begin,**counts};out.append(result);print(result,flush=True)
 if status=='UNKNOWN':break
assert all(hashlib.sha256((P/f).read_bytes()).hexdigest()==h for f,h in pins.items())
(O/'results.json').write_text(json.dumps({'results':out,'seconds':time.monotonic()-start,'pins':pins,'nodes':nodes,'unvisited_branches':5-len(out),'method':'Independent complete empty slot enumeration, reverse static heavy requests, direct legality, reverse forced propagation, whole degree row branching; no author search imports'},indent=2)+'\n')
