import itertools,json,hashlib
from pathlib import Path
p=Path(__file__).parent
masks=[7,25,10,18,12,20]
classes=[['a0','b0','f0','g0a','g0b','g0c'],['f1','c1','g1a','g1b','g1c'],['b2','f2','c2','g2a','g2b'],['f3','d3','e3','g3a','g3b'],['b4','f4','d4','e4','g4']]
names=['h'+str(c) for c in range(5)]+list('ABCDEF')+sum(classes,[]);idx={n:i for i,n in enumerate(names)}
g=[set() for _ in names]
def add(a,b):a=idx[a];b=idx[b];g[a].add(b);g[b].add(a)
for h,m in zip('ABCDEF',masks):
 for c in range(5):
  if m>>c&1:add(h,'h'+str(c))
for a,b in [('A','D'),('A','E'),('B','C')]:add(a,b)
for c,ns in enumerate(classes):
 for n in ns:add(n,'h'+str(c))
for h,ns in {'A':['a0'],'B':['b0','b2','b4'],'C':['c1','c2'],'D':['d3','d4'],'E':['e3','e4'],'F':['f'+str(c) for c in range(5)]}.items():
 for n in ns:add(h,n)
def clean(graph):return all(len(graph[a]&graph[b])<=1 for a,b in itertools.combinations(range(len(names)),2))
assert clean(g)
def match(ns):
 if not ns:yield [];return
 for i in range(1,len(ns)):
  for rest in match(ns[1:i]+ns[i+1:]):yield [(ns[0],ns[i])]+rest
profiles=[];options=[]
for c,ns in enumerate(classes):
 eligible=[n for n in ns if not g[idx[n]]&g[idx['h'+str(c)]]]
 exempt=[n for n in ns if n not in eligible]
 assert len(eligible)%2==0
 valid=[]
 for edges in match(eligible):
  trial=[x.copy() for x in g]
  for a,b in edges:trial[idx[a]].add(idx[b]);trial[idx[b]].add(idx[a])
  if clean(trial):valid.append(edges)
 profiles.append(dict(colour=c,vertices=ns,exempt=exempt,eligible=eligible,allowed_matchings=valid))
 options.append(valid)
assert [len(x) for x in options]==[3,3,2,3,1]
assert profiles[2]['exempt']==['f2']
assert profiles[4]['exempt']==['b4','f4','d4']
assert options[4]==[[('e4','g4')]]
results=[]
for af,bf in itertools.product([3,4],[1,2]):
 count=0;types=set()
 for choice in itertools.product(*options):
  trial=[x.copy() for x in g]
  for a,b in sum(choice,[])+[('f1','f3'),('a0','f'+str(af)),('b0','f'+str(bf))]:
   trial[idx[a]].add(idx[b]);trial[idx[b]].add(idx[a])
  if clean(trial):
   count+=1;types.add(any(set(edge)=={'f3','d3'} for edge in choice[3]))
 results.append(dict(af=af,bf=bf,matching_completions=count,f3_d3_edge_possibilities=sorted(types)))
result=dict(scope='Universal no-C/F-sharing core44 within-colour matching lemma; partial37vertex graphs only, no empty incidence or whole branch exclusion.',profiles=profiles,combined_results=results,names=names,base_adjacency=[sorted(x) for x in g])
(p/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['names','base_adjacency']},indent=2))
