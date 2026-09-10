import pathlib,json,itertools,hashlib,collections
P=pathlib.Path('/tmp/erdos85-sol1-core44-colour-matchings')
for f,h in json.loads((P/'pins.json').read_text()).items():assert hashlib.sha256((P/f).read_bytes()).hexdigest()==h
r=json.loads((P/'results.json').read_text());names=r['names'];idx={n:i for i,n in enumerate(names)}
g=[set() for _ in names]
def edge(a,b):u=idx[a];v=idx[b];g[u].add(v);g[v].add(u)
for h,support in zip('ABCDEF',[(0,1,2),(0,3,4),(1,3),(1,4),(2,3),(2,4)]):
 for c in support:edge(h,'h'+str(c))
for a,b in [('A','D'),('A','E'),('B','C')]:edge(a,b)
classes=[]
for c in range(5):
 ns=[n for n in names[11:] if n[1]==str(c)];classes.append(ns)
 for n in ns:edge(n,'h'+str(c))
for h,ns in [('A',['a0']),('B',['b0','b2','b4']),('C',['c1','c2']),('D',['d3','d4']),('E',['e3','e4']),('F',['f'+str(c) for c in range(5)])]:
 for n in ns:edge(h,n)
assert [sorted(ns) for ns in g]==r['base_adjacency']
def clean(graph):return all(len(graph[u]&graph[v])<=1 for u,v in itertools.combinations(range(37),2))
options=[]
for c,ns in enumerate(classes):
 eligible=[idx[n] for n in ns if not g[idx[n]]&g[c]];pairs=list(itertools.combinations(eligible,2));found=[]
 for selected in itertools.combinations(pairs,len(eligible)//2):
  counts=collections.Counter(v for e in selected for v in e)
  if set(counts)!=set(eligible) or any(d!=1 for d in counts.values()):continue
  trial=[set(a) for a in g]
  for u,v in selected:trial[u].add(v);trial[v].add(u)
  if clean(trial):found.append(selected)
 assert len(found)==len(r['profiles'][c]['allowed_matchings'])
 options.append(found)
def canonical(edges,c):
 free=[idx[n] for n in classes[c] if n.startswith('g')];keys=[]
 for perm in itertools.permutations(free):
  mapping=dict(zip(free,perm));keys.append(tuple(sorted(tuple(sorted((mapping.get(u,u),mapping.get(v,v)))) for u,v in edges)))
 return min(keys)
audits=[]
for af,bf in itertools.product([3,4],[1,2]):
 orbits=collections.Counter();count=0
 for choice in itertools.product(*options):
  trial=[set(ns) for ns in g]
  for u,v in list(itertools.chain.from_iterable(choice))+[(idx['f1'],idx['f3']),(idx['a0'],idx['f'+str(af)]),(idx['b0'],idx['f'+str(bf)])]:trial[u].add(v);trial[v].add(u)
  assert clean(trial);count+=1
  orbits[tuple(canonical(choice[c],c) for c in range(5))]+=1
 assert count==54 and sorted(orbits.values())==[18,36]
 audits.append(dict(af=af,bf=bf,labelled=count,canonical_types=len(orbits),orbit_sizes=sorted(orbits.values())))
out=dict(status='PASS',source_pins='all match',independent_method='edge-subset perfect degree covers and explicit within-colour free-vertex permutation orbits',matching_counts=list(map(len,options)),audits=audits,scope='Necessary naming cover only; no branch exclusion or full graph')
print(out)
pathlib.Path(__file__).with_name('REVIEW2054.json').write_text(json.dumps(out,indent=2)+'\n')
