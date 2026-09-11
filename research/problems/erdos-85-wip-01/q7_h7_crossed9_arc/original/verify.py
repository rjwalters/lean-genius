"""Direct set certificate replay and independent local-negative subset checks."""
import pathlib,json,gzip,itertools,time,hashlib
P=pathlib.Path(__file__).parent
for name,h in json.loads((P/'input-pins.json').read_text()).items():assert hashlib.sha256((P/name).read_bytes()).hexdigest()==h
with gzip.open(P/'results.json.gz','rt') as f:data=json.load(f)
profile=next(r for r in json.loads((P/'profile-source.json').read_text())['results'] if not r['twins_adjacent'] and r['profile_index']==9)
sd=json.loads((P/'seed-source.json').read_text());base=next(r['adjacency'] for r in sd['patterns'] if not r['twins_adjacent']);idx={n:i for i,n in enumerate(sd['names'])};hosts=sorted(base[0]);outside=set(range(7,49))-set(hosts)
assert [r['assignment_index'] for r in data['results']]==list(range(data['summary']['visited']))
rows=failures=events=local_nodes=negatives=0;start=time.monotonic()
for r in data['results']:
 g=list(map(set,r['adjacency']));a=profile['assignments'][r['assignment_index']]
 # All high incidences and induced host edges must match the fixed seed;
 # pair host ownership must recover the precise source partition.
 assert all(g[c]==set(base[c]) for c in range(7))
 for j,h in enumerate(hosts):
  assert g[h]&set(hosts)==set(base[h])&set(hosts) and len(g[h])==7
  assert sum(1<<e for e,(x,y) in enumerate(profile['edge_order']) if idx[f'P{x}{y}'] in g[h])==a[j]
 assert all(len(g[u]&set(hosts))==1 and not g[u]&outside for u in outside)
 assert all(u!=v and u in g[v] for u in range(49) for v in g[u])
 assert all(len(g[u]&g[v])<=1 for u in range(49) for v in range(u))
 if r['status']=='UNKNOWN':continue
 assert r['nodes']<=100000
 if r['status']=='INFEASIBLE_LOCAL':
  u=r['local_result']['vertex'];candidates=[v for v in sorted(outside) if v!=u and all(not g[v]&g[w] for w in g[u])];need=7-len(g[u]);count=0;found=0;deadline=time.monotonic()+60
  def subsets(k,selected):
   global count,found
   count+=1
   if count>100000 or time.monotonic()>deadline:raise TimeoutError
   if len(selected)==need:
    ns=g[u]|set(selected)
    if all(len(ns&g[c])==1 for c in range(7)):found+=1
    return
   for j in range(k,len(candidates)-(need-len(selected))+1):
    v=candidates[j]
    if all(not g[v]&g[w] for w in selected):subsets(j+1,selected+[v])
  subsets(0,[]);assert found==0;local_nodes+=count;negatives+=1;continue
 assert r['status']=='INFEASIBLE_ARC'
 domains={int(u):[{v for v in outside if m>>v&1} for m in ms] for u,ms in r['initial'].items()};assert set(domains)==outside
 for u,choices in domains.items():
  for choice in choices:
   assert len(choice)==7-len(g[u]) and u not in choice
   ns=g[u]|choice
   assert all(not ((g[v]-{u})&(g[w]-{u})) for v,w in itertools.combinations(ns,2))
   assert all(len(ns&g[c])==1 for c in range(7));rows+=1
 for e in r['events']:
  u,v=e['vertex'],e['against'];assert u!=v;bad=[{w for w in outside if m>>w&1} for m in e['removed']]
  for choice in bad:
   assert choice in domains[u]
   for other in domains[v]:
    assert ((v in choice)!=(u in other)) or len((g[u]|choice)&(g[v]|other))>1
    failures+=1
  domains[u]=[c for c in domains[u] if c not in bad];events+=1
 assert not domains[r['empty_vertex']]
 if (r['assignment_index']+1)%500==0:print('verified',r['assignment_index']+1,flush=True)
out=dict(verified_assignments=len(data['results']),verified_rows=rows,verified_deletion_events=events,verified_failed_supports=failures,independent_local_negatives=negatives,local_subset_nodes=local_nodes,seconds=time.monotonic()-start,scope='Directset row soundness/arc replay and independent local-negative enumeration. Independent completeness of row domains and host cover remain reviewer premises.')
(P/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
