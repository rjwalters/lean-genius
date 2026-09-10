from pathlib import Path
import json,itertools,hashlib
p=Path(__file__).parent
# Independent minimal named graph: five highs, B,C,F, their three B specials,
# two C singletons, five F singletons, and two heavy-free S2 vertices.
names=['h0','h1','h2','h3','h4','B','C','F','b0','b2','b4','c1','c2','f0','f1','f2','f3','f4','p','q'];idx={n:i for i,n in enumerate(names)}
g=[set() for _ in names]
def edge(a,b):a=idx[a];b=idx[b];g[a].add(b);g[b].add(a)
for h,cs in [('B',[0,3,4]),('C',[1,3]),('F',[2,4])]:
 for c in cs:edge(h,'h'+str(c))
edge('B','C')
for h,vs in [('B',['b0','b2','b4']),('C',['c1','c2']),('F',['f0','f1','f2','f3','f4'])]:
 for v in vs:edge(h,v);edge(v,'h'+v[1])
for v in ['p','q']:edge(v,'h2')
def clean(graph):return all(len(graph[a]&graph[b])<=1 for a,b in itertools.combinations(range(len(names)),2))
assert clean(g)
source=['b0','b2','b4'];target=['b2','f2','c2','p','q'];allowed={}
for v in source:
 allowed[v]=[]
 for w in target:
  if v==w:continue
  h=[x.copy() for x in g];a=idx[v];b=idx[w];h[a].add(b);h[b].add(a)
  if clean(h):allowed[v].append(w)
assert allowed=={'b0':['f2','p','q'],'b2':['p','q'],'b4':['p','q']}
valid=[]
for ts in itertools.permutations(target,3):
 if not all(t in allowed[s] for s,t in zip(source,ts)):continue
 h=[x.copy() for x in g]
 for s,t in zip(source,ts):a=idx[s];b=idx[t];h[a].add(b);h[b].add(a)
 if clean(h):valid.append(dict(zip(source,ts)))
assert len(valid)==2 and all(r['b0']=='f2' for r in valid)
edge('b0','f1')
assert clean(g)
a=idx['b0'];b=idx['f2'];g[a].add(b);g[b].add(a)
assert not clean(g)
out=dict(allowed_targets=allowed,injective_assignments_examined=60,valid_assignments=valid,bf1_conflict='b0-f1-F-f2-b0',scope='No-C/F-sharing core44 forces b0-f2; excludes bf1 universally. Tiny direct minimal graph check supplements the paper proof; no completion search or Lean theorem.')
(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
