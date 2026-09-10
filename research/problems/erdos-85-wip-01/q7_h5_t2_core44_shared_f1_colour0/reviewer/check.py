from pathlib import Path
import json,itertools,hashlib,time
p=Path(__file__).parent;s=Path('/Users/rwalters/lean-genius-q7-outside-first-20260910/core44-colour0-shared1');pins=json.loads((s/'pins.json').read_text());assert all(hashlib.sha256((s/f).read_bytes()).hexdigest()==h for f,h in pins.items())
br=[r for r in json.loads((s/'branches.json').read_text())['results'] if r['shared']==1 and r['omitted']==7 and r['internal']==[] and r['af']==4 and r['bf']==2];assert len(br)==1
sets=list(map(set,br[0]['adjacency']))+[set() for _ in range(3)]
def add_set(u,v):sets[u].add(v);sets[v].add(u)
for v in (32,33,34):add_set(0,v)
for u,v in [(27,32),(28,33),(33,34),(30,34)]:add_set(u,v)
slots=[]
for c in range(1,5):
 for h in (23,24,27,32,33,34):
  if not sets[h]&sets[c]:
   v=len(sets);sets.append(set());add_set(v,c);add_set(v,h);slots.append((v,c,h))
assert len(sets)==49
frozen=json.loads((s/'skeletons.json').read_text())['results'];assert len(frozen)==1 and [sorted(ns) for ns in sets]==frozen[0]['adjacency']
base=[sum(1<<v for v in ns) for ns in sets]
def bits(x):
 while x:b=x&-x;yield b.bit_length()-1;x^=b
def clean(g):return all((g[u]&g[v]).bit_count()<=1 for u,v in itertools.combinations(range(49),2))
def add(g,u,v):g[u]|=1<<v;g[v]|=1<<u
assert clean(base)
empty=[v for v in range(11,23) if not base[v]&base[0]];assert len(empty)==5
counts=dict(empty_assignments=0,empty_survivors=0,raw_heavy_products=0,heavy_leaves=0,forced_edges=0,contradictions=0,fixed_points=0);start=time.monotonic()
def force(g):
 while True:
  if time.monotonic()-start>60:raise TimeoutError
  deg=[x.bit_count() for x in g]
  assert clean(g)
  forced=None
  for u in range(48,4,-1):
   if deg[u]>7:return False
   candidates=[]
   for v in range(48,4,-1):
    if v==u or deg[u]>=7 or deg[v]>=7 or g[u]>>v&1:continue
    # Full direct pair tests after hypothetical insertion, not author domain helper.
    h=g.copy();add(h,u,v)
    if clean(h):candidates.append(v)
   if len(candidates)<7-deg[u]:return False
   for c in range(4,-1,-1):
    if g[u]&g[c]:continue
    cs=[v for v in candidates if g[v]>>c&1]
    if not cs:return False
    if len(cs)==1:forced=(u,cs[0]);break
   if forced:break
   if candidates and len(candidates)==7-deg[u]:forced=(u,candidates[-1]);break
  if forced:add(g,*forced);counts['forced_edges']+=1
  else:return True
requests=[(7,2),(8,3),(8,4),(9,3),(9,4)]
status='COMPLETE'
try:
 for pair in itertools.combinations(empty,2):
  for rest in itertools.permutations([v for v in empty if v not in pair]):
   counts['empty_assignments']+=1;g=base.copy()
   for u,vs in [(27,pair),(32,[rest[0]]),(33,[rest[1]]),(34,[rest[2]])]:
    for v in vs:add(g,u,v)
   if not clean(g):continue
   counts['empty_survivors']+=1
   for selected in itertools.product(*[[v for v in range(35,49) if g[v]&31==1<<c] for _,c in requests]):
    counts['raw_heavy_products']+=1;h=g.copy()
    for (u,c),v in zip(requests,selected):add(h,u,v)
    if not clean(h) or any(x.bit_count()>7 for x in h[5:]):continue
    counts['heavy_leaves']+=1
    if force(h):counts['fixed_points']+=1
    else:counts['contradictions']+=1
except TimeoutError:status='UNKNOWN'
assert all(hashlib.sha256((s/f).read_bytes()).hexdigest()==h for f,h in pins.items())
out=dict(status=status,counts=counts,seconds=time.monotonic()-start,source_pins=pins,scope='Independent reconstruction, all60 empty assignments, raw Cartesian heavy assignment enumeration, direct all-pair candidate insertion tests, reverse forcing from EVERY heavy leaf; no author imports or100-leaf filter.')
(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='source_pins'},indent=2))
