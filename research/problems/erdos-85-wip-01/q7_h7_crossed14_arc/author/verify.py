"""Independent direct-set verification of deletion certificates (no filter import)."""
import pathlib,json,gzip,hashlib,itertools,time
P=pathlib.Path(__file__).parent;S=pathlib.Path('/tmp/erdos85-sol1-h7-crossed14-local/results.json');raw=S.read_bytes();source=json.loads(raw)
with gzip.open(P/'results.json.gz','rt') as f:data=json.load(f)
assert hashlib.sha256(raw).hexdigest()==data['summary']['source_sha256']
expected={i for i,r in enumerate(source['results']) if r['status']=='LOCAL_FEASIBLE'}
assert {r['source_index'] for r in data['results']}==expected and len(data['results'])==len(expected)==448
rows=failures=events=0;start=time.monotonic()
for result in data['results']:
 assert result['status']=='INFEASIBLE_ARC' and result['nodes']<=100000
 g=list(map(set,source['results'][result['source_index']]['adjacency']));outside=set(range(7,49))-g[0]
 domains={int(u):[{v for v in outside if m>>v&1} for m in masks] for u,masks in result['initial'].items()}
 assert set(domains)==outside
 for u,choices in domains.items():
  for choice in choices:
   assert len(choice)==7-len(g[u]) and u not in choice
   # Adding a star can only create a C4 with two neighbours of its centre.
   neighbours=g[u]|choice
   assert all(not ((g[v]-{u})&(g[w]-{u})) for v,w in itertools.combinations(neighbours,2))
   assert all(len(neighbours&g[c])==1 for c in range(7))
   rows+=1
 for event in result['events']:
  u,v=event['vertex'],event['against'];bad=[{w for w in outside if m>>w&1} for m in event['removed']]
  for choice in bad:
   assert choice in domains[u]
   for other in domains[v]:
    assert ((v in choice)!=(u in other)) or len((g[u]|choice)&(g[v]|other))>1
    failures+=1
  domains[u]=[c for c in domains[u] if c not in bad];events+=1
 assert not domains[result['empty_vertex']]
out=dict(verified_assignments=448,verified_rows=rows,verified_deletion_events=events,verified_failed_supports=failures,seconds=time.monotonic()-start,scope='Row soundness and every arc deletion verified directly; completeness requires exhaustive generator audit or independent enumeration.')
(P/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
