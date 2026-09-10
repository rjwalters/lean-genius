import pathlib,json,itertools,time,hashlib,math
P=pathlib.Path('/tmp/erdos85-sol1-core44-owncolour-empty');O=pathlib.Path(__file__).parent
pins=json.loads((P/'pins.json').read_text());assert all(hashlib.sha256((P/f).read_bytes()).hexdigest()==h for f,h in pins.items())
cd=json.loads((P/'canonical-source.json').read_text());saved=json.loads((P/'results.json').read_text())['results']
names=cd['names']+['E'+str(i) for i in range(12)];ix={n:i for i,n in enumerate(names)}
start=time.monotonic();nodes=0;out=[]
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


for typ in [False,True]:
 for omitted in [4,7,11,0]:
  g=[0]*49
  def edge(a,b):add(g,ix[a],ix[b])
  for h,cs in [('A',[0,1,2]),('B',[0,3,4]),('C',[1,3]),('D',[1,4]),('E',[2,3]),('F',[2,4])]:
   for c in cs:edge(h,'h'+str(c))
  for name in names[11:37]:
   c=next(x for x in name if x.isdigit());edge(name,'h'+c)
  for a,b in [('A','D'),('A','E'),('B','C')]:edge(a,b)
  for h,vs in [('A',['a0']),('B',['b0','b2','b4']),('C',['c1','c2']),('D',['d3','d4']),('E',['e3','e4']),('F',['f'+str(i) for i in range(5)])]:
   for v in vs:edge(h,v)
  matching=[('f0','g0a'),('g0b','g0c'),('f1','g1a'),('g1b','g1c'),('b2','g2a'),('c2','g2b'),('e4','g4')]
  matching+= [('f3','d3'),('g3a','g3b')] if typ else [('f3','g3a'),('d3','g3b')]
  for a,b in matching+[('f1','f3'),('a0','f3'),('b0','f2')]:edge(a,b)
  can=[r for r in cd['canonical_configurations'] if r['af']==3 and r['bf']==2 and r['f3_d3_edge']==typ];assert len(can)==1
  assert [list(bits(x)) for x in g[:37]]==can[0]['adjacency']
  for h,es in [('A',[0]),('C',[5,8]),('D',[1,2]),('E',[3,4]),('a0',[5,6,7]),('b0',[1,3,9]),('b2',[2,6,10]),('b4',[e for e in [0,4,7,11] if e!=omitted])]:
   for e in es:edge(h,'E'+str(e))
  for e in [8,9,10,11]:edge('E0','E'+str(e))
  original=[r for r in saved if r['omitted']==omitted and r['f3_d3_edge']==typ];assert len(original)==1 and g==original[0]['initial']
  assert clean(g) and all(g[h].bit_count()==8 for h in range(5))
  begin=nodes
  try:status='FOUND' if solve(g) else 'EXHAUSTED'
  except TimeoutError:status='UNKNOWN'
  r={'f3_d3_edge':typ,'omitted':omitted,'status':status,'nodes':nodes-begin};out.append(r);print(r,flush=True)
  if status=='UNKNOWN':break
 if out[-1]['status']=='UNKNOWN':break
assert all(hashlib.sha256((P/f).read_bytes()).hexdigest()==h for f,h in pins.items())
(O/'results.json').write_text(json.dumps({'results':out,'nodes':nodes,'seconds':time.monotonic()-start,'unvisited':8-len(out),'pins':pins,'method':'Independent name-based reconstruction of all heavy, singleton, own-colour and distinguished-empty edges; reverse forcing and whole-degree-row search from initial graphs, no author imports or forced-state inputs.'},indent=2)+'\n')
