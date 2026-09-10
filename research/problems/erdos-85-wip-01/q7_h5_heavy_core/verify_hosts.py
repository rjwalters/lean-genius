"""Independent matching test and direct 49-vertex adjacency verification."""
import itertools,json,hashlib,time
from pathlib import Path

def feasible(masks,adj,capacities):
 n=len(masks);pairlist=list(itertools.combinations(range(n),2));pairid={p:i for i,p in enumerate(pairlist)};choices=[]
 for colour in range(5):
  required=[v for v in range(n) if sum(bool(masks[w]>>colour&1) for w in adj[v])==0]
  k=max(0,len(required)-capacities[colour])
  if 2*k>len(required):return False
  allowed=[(u,v) for u,v in itertools.combinations(required,2) if not(masks[u]&masks[v]) and not(adj[u]&adj[v])]
  options=[]
  for matching in itertools.combinations(allowed,k):
   vertices=[v for edge in matching for v in edge]
   if len(set(vertices))==2*k:options.append(sum(1<<pairid[e] for e in matching))
  if not options:return False
  choices.append(options)
 choices.sort(key=len);states={0}
 for options in choices:
  states={old|option for old in states for option in options if not old&option}
  if not states:return False
 return True

def check_graph(masks,adj,capacities,hosts):
 supports=masks+[1<<c for c in range(5) for _ in range(capacities[c])]
 supports += [0]*(44-len(supports));assert len(supports)==44
 graph=[set() for _ in range(49)]
 def edge(u,v):assert u!=v;graph[u].add(v);graph[v].add(u)
 for v,mask in enumerate(supports,5):
  for c in range(5):
   if mask>>c&1:edge(c,v)
 for u in range(len(masks)):
  for v in adj[u]:edge(5+u,5+v)
 offset=5+len(masks)
 for colour,groups in enumerate(hosts):
  assert len(groups)<=capacities[colour]
  for i,group in enumerate(groups):
   assert len(group)==len(set(group)) and len(group)<=2
   for heavy in group:edge(offset+i,5+heavy)
  offset+=capacities[colour]
 assert all(len(graph[c])==8 for c in range(5))
 for u,v in itertools.combinations(range(49),2):assert len(graph[u]&graph[v])<=1,(u,v)
 for v,mask in enumerate(supports,5):assert len(graph[v])<=7
 for v in range(5,5+len(masks)):
  for c in range(5):assert len(graph[v]&graph[c])==1,(v,c)
 return hashlib.sha256(json.dumps([sorted(n) for n in graph],separators=(',',':')).encode()).hexdigest()

start=time.monotonic();output=[]
for sector in [0,2]:
 source=json.loads(Path(f'core-t{sector}.json').read_text());raw=Path(f'hosts-t{sector}.json').read_bytes();pilot=json.loads(raw)
 assert pilot['unvisited']==0 and len(pilot['results'])==len(source['canonical_cores'])
 assert [r['core'] for r in pilot['results']]==source['canonical_cores']
 masks=source['masks'];triples=[m for m in masks if m.bit_count()==3];capacities=[4+sum(bool(m>>c&1) for m in triples) for c in range(5)]
 rows=[]
 for row in pilot['results']:
  adj=[set() for _ in masks]
  for i,(u,v) in enumerate(itertools.combinations(range(len(masks)),2)):
   if row['core']>>i&1:adj[u].add(v);adj[v].add(u)
  possible=feasible(masks,adj,capacities);assert possible==(row['status']=='PARTIAL_WITNESS'),row['core']
  item=dict(core=row['core'],independent_feasible=possible)
  if possible:item['partial_graph_sha256']=check_graph(masks,adj,capacities,row['hosts'])
  rows.append(item)
 output.append(dict(sector=sector,pilot_sha256=hashlib.sha256(raw).hexdigest(),checked=len(rows),feasible=sum(r['independent_feasible'] for r in rows),results=rows))
Path('host-verification.json').write_text(json.dumps(dict(seconds=time.monotonic()-start,sectors=output,scope='Independent minimum-size matching feasibility plus direct partial-graph C4/high-degree/BC checks'),indent=2)+'\n')
print(json.dumps([{k:v for k,v in r.items() if k!='results'} for r in output],indent=2))
