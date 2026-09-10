import pathlib,json,itertools,hashlib
P=pathlib.Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/t2-core44-structure')
for f,h in json.loads((P/'pins.json').read_text()).items():assert hashlib.sha256((P/f).read_bytes()).hexdigest()==h
ours=json.loads(pathlib.Path('/Users/rwalters/lean-genius-q7-outside-first-20260910/core44-special-projection/four-pattern-results.json').read_text())['results']
author={x['omitted']:set(map(tuple,x['edges'])) for x in json.loads((P/'patterns.json').read_text())}
def perm(v):return v if v<11 else (v+4 if v<23 else v-12)
for r in ours:
 edges={tuple(sorted((perm(u),perm(v)))) for u,ns in enumerate(r['skeleton']) for v in ns if u<v}
 assert edges==author[r['omitted']]
# Exhaust row assignments before normalization, using direct C4 checks only.
g=list(map(set,ours[0]['skeleton']))
for v in [7,24,25,26]:
 for e in list(g[v]&set(range(11,23))):g[v].remove(e);g[e].remove(v)
def clean():return all(len(g[u]&g[v])<=1 for u,v in itertools.combinations(range(27),2))
assert clean()
counts={0:0,4:0,7:0,11:0};leaves=0
def walk(todo):
 global leaves
 if not todo:
  ce=g[7]&set(range(11,23));b0=g[24]&set(range(11,23));b2=g[25]&set(range(11,23));b4=g[26]&set(range(11,23))
  D={12,13};E={14,15};A={16,17,18};R={19,20,21,22}
  assert [len(ce&x) for x in [D,E,A,R]]==[0,0,1,1]
  assert [len(b0&x) for x in [D,E,A,R]]==[1,1,0,1]
  assert [len(b2&x) for x in [D,E,A,R]]==[1,0,1,1]
  unused=set(range(11,23))-(ce|b0|b2|b4);assert len(unused)==1
  missing=unused.pop();kind=0 if missing==11 else 4 if missing in E else 7 if missing in A else 11
  counts[kind]+=1;leaves+=1;return
 v,n=todo[0]
 for es in itertools.combinations(range(11,23),n):
  if any(any(g[e]&g[w] for w in g[v]) for e in es):continue
  if any(g[e]&g[f] for e,f in itertools.combinations(es,2)):continue
  for e in es:g[v].add(e);g[e].add(v)
  walk(todo[1:])
  for e in es:g[v].remove(e);g[e].remove(v)
walk([(7,2),(24,3),(25,3),(26,3)])
assert leaves==2304 and set(counts.values())=={576}
for row in json.loads((P/'empty-results.json').read_text())['results']:
 graph=[set() for _ in range(27)]
 edges=set(map(tuple,row['edges']))
 assert author[row['omitted']]<=edges
 for u,v in edges:graph[u].add(v);graph[v].add(u)
 assert all(len(graph[u]&graph[v])<=1 for u,v in itertools.combinations(range(27),2))
 for e in range(15,27):
  heavy=graph[e]&set(range(5,11))
  degree=2+sum(len(graph[h]&set(range(5)))-1 for h in heavy)
  assert len(graph[e]&set(range(15,27)))==degree
res={'status':'PASS','pins':'all match','canonical_graphs':'exact match under fixed vertex relabeling','labeled_distinguished_row_assignments':leaves,'omitted_type_counts':counts,'author_positive_graphs':'all four direct checked against skeleton, C4 and derived empty degrees','scope':'Four-pattern cover and partial witnesses, no core exclusion or Lean claim'}
print(res)
pathlib.Path(__file__).with_name('REVIEW2046.json').write_text(json.dumps(res,indent=2)+'\n')
