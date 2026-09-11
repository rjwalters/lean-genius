"""Independent certificate verification with exact integer neighbourhood sets."""
import pathlib,json,gzip,hashlib,time,collections
P=pathlib.Path(__file__).parent
for f,h in json.loads((P/'input-pins.json').read_text()).items():assert hashlib.sha256((P/f).read_bytes()).hexdigest()==h
profile=json.loads((P/'profile-source.json').read_text())['results'][0];sd=json.loads((P/'seed-source.json').read_text());base=next(s['adjacency'] for s in sd['patterns'] if s['twins_adjacent']==profile['twins_adjacent']);idx={n:i for i,n in enumerate(sd['names'])};hosts=sorted(base[0]);H=sum(1<<h for h in hosts);outside=sorted(set(range(7,49))-set(hosts))
def bits(m):
 while m:
  b=m&-m;yield b.bit_length()-1;m-=b
with gzip.open(P/'results.json.gz','rt') as f:data=json.load(f)
assert [r['assignment_index'] for r in data['results']]==list(range(data['summary']['visited']))
start=time.monotonic();rows=events=failures=local_nodes=0;counts=collections.Counter()
for result in data['results']:
 i=result['assignment_index'];g=[sum(1<<v for v in ns) for ns in result['adjacency']];counts[result['status']]+=1
 assert all(g[c]==sum(1<<v for v in base[c]) for c in range(7))
 assert all(not(g[u]>>u&1) and all(g[v]>>u&1 for v in bits(g[u])) for u in range(49))
 assert all((g[u]&g[v]).bit_count()<=1 for u in range(49) for v in range(u))
 for h,m in zip(hosts,profile['assignments'][i]):
  assert g[h].bit_count()==7 and (g[h]&H).bit_count()==1
  assert m==sum(1<<e for e,(a,b) in enumerate(profile['edge_order']) if g[h]>>idx[f'P{a}{b}']&1)
 assert all((g[u]&H).bit_count()==1 and g[u]&~(127|H)==0 for u in outside)
 if result['status']=='UNKNOWN':continue
 assert result['nodes']<=100000
 if result['status']=='INFEASIBLE_LOCAL':
  u=result['local_result']['vertex'];existing=list(bits(g[u]));candidates=[v for v in outside if u!=v and all(not g[v]&g[w] for w in existing)];need=7-g[u].bit_count();nodes=0;found=0;deadline=time.monotonic()+60
  def subsets(k,chosen,neighbour_union):
   global nodes,found
   nodes+=1
   if nodes>100000 or time.monotonic()>deadline:raise TimeoutError
   if len(chosen)==need:
    ns=g[u]|sum(1<<v for v in chosen)
    if all((ns&g[c]).bit_count()==1 for c in range(7)):found+=1
    return
   for j in range(k,len(candidates)-(need-len(chosen))+1):
    v=candidates[j]
    if not g[v]&neighbour_union:subsets(j+1,chosen+[v],neighbour_union|g[v])
  subsets(0,[],0);assert found==0;local_nodes+=nodes;continue
 assert result['status']=='INFEASIBLE_ARC'
 domains={int(u):set(ms) for u,ms in result['initial'].items()};assert set(domains)==set(outside)
 for u,choices in domains.items():
  assert len(choices)==len(result['initial'][str(u)])
  for row in choices:
   assert row.bit_count()==7-g[u].bit_count() and not(row>>u&1) and not row&(127|H)
   ns=g[u]|row;seen=0
   for v in bits(ns):
    neighbourhood=g[v]&~(1<<u);assert not seen&neighbourhood;seen|=neighbourhood
   assert all((ns&g[c]).bit_count()==1 for c in range(7));rows+=1
 for event in result['events']:
  u,v=event['vertex'],event['against'];assert u!=v
  removed=set(event['removed']);assert len(removed)==len(event['removed']) and removed<=domains[u]
  for a in removed:
   full_a=g[u]|a
   for b in domains[v]:
    assert ((a>>v)&1)!=((b>>u)&1) or (full_a&(g[v]|b)).bit_count()>1
    failures+=1
  domains[u]-=removed;events+=1
 assert not domains[result['empty_vertex']]
 if (i+1)%2000==0:print('verified',i+1,round(time.monotonic()-start,2),flush=True)
out=dict(status='PASS',verified_assignments=len(data['results']),counts=dict(counts),verified_rows=rows,verified_events=events,verified_failed_supports=failures,independent_local_subset_nodes=local_nodes,seconds=time.monotonic()-start,scope='Exact neighbourhood-set row soundness and all deletion receipts; local negatives independently enumerated. Domain completeness needs separate independent review.')
(P/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
