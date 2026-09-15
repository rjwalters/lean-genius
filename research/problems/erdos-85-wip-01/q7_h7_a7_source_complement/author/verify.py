"""Audit unchanged search body, exact source partition, and every saved graph."""
import hashlib,json,itertools,time,collections
from pathlib import Path
P=Path(__file__).parent
launch=json.loads((P/'launch.json').read_text());S=Path(launch['source'])
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in launch['source_pins'].items():assert sha(S/n)==h
assert sha(P/'complete.py')==launch['driver_sha256']
oldcode=(S/'complete.py').read_text();newcode=(P/'complete.py').read_text()
assert oldcode[oldcode.index(' base=[0]*21'):oldcode.index(' out.append(')]==newcode[newcode.index(' base=[0]*21'):newcode.index(' row=dict(')]
source=json.loads((S/'results.json').read_text());old=json.loads((S/'completion-results.json').read_text());new=json.loads((P/'completion-results.json').read_text())
known={r['source_index']:r for r in old['results'] if r['status']=='COMPLETE'}
assert set(known)==set(range(860))
queue=json.loads((P/'queue.json').read_text());assert queue==list(range(860,1310))
assert [r['source_index'] for r in new['results']]==queue[:new['summary']['visited']]
assert new['summary']['unvisited']==450-len(new['results'])
start=time.monotonic();deadline=start+120
pins={str(p):sha(p) for p in [P/'complete.py',P/'launch.json',P/'queue.json',P/'completion-results.json']}
with (P/'verification-launch.json').open('x') as f:json.dump({'aggregate_seconds':120,'input_pins':pins},f,indent=2)
ngraph=0;counts=collections.Counter();shape=collections.defaultdict(collections.Counter)
for r in new['results']:
 assert time.monotonic()<deadline
 si=r['source_index'];rep=source['representatives'][si]
 assert r['F_index']==rep['F_index'] and r['status'] in ('COMPLETE','UNKNOWN')
 assert r['nodes']<=100001 and (r['status']!='COMPLETE' or r['nodes']<=100000)
 assert r['count']==len(r['solutions']) and len({tuple(map(tuple,es)) for es in r['solutions']})==r['count']
 base=[[False]*21 for _ in range(21)]
 for u,v in rep['F_edges']:base[u][v]=base[v][u]=True
 for s,hs in enumerate(rep['singleton_hosts'],7):
  for e in hs:base[s][e]=base[e][s]=True
 target={u:5-sum(base[u]) for u in range(7,21)}
 for es in r['solutions']:
  g=[row[:] for row in base]
  assert len(set(map(tuple,es)))==len(es)
  for u,v in es:
   assert 7<=u<v<21 and not g[u][v];g[u][v]=g[v][u]=True
  assert all(sum(g[u])==target[u] for u in target)
  # independent Boolean common-neighbor test, rather than producer bitset pruning
  assert all(sum(g[u][w] and g[v][w] for w in range(21))<=1 for u in range(21) for v in range(u))
  ngraph+=1
 counts[r['status']]+=1
 if si==860 and r['status']=='COMPLETE':
  partial=next(x for x in old['results'] if x['source_index']==860)
  assert set(tuple(map(tuple,x)) for x in partial['solutions'])<=set(tuple(map(tuple,x)) for x in r['solutions'])
assert dict(counts)==new['summary']['counts']
bynew={r['source_index']:(i,r) for i,r in enumerate(new['results'])}
rows=[]
for si,rep in enumerate(source['representatives']):
 if si in known:status='COMPLETE';origin='original2116';ri=si;count=known[si]['count']
 elif si in bynew:ri,r=bynew[si];status=r['status'];origin='new-complement';count=r['count']
 else:status='UNVISITED';origin=None;ri=None;count=None
 rows.append({'source_index':si,'F_index':rep['F_index'],'status':status,'origin':origin,'record_index':ri,'saved_graphs':count})
 shape[rep['F_index']][status]+=1
assert len(rows)==1310 and len({r['source_index'] for r in rows})==1310
for n,h in pins.items():assert sha(Path(n))==h
coverage={'status':'PASS_EXACT_SOURCE_PARTITION','original_complete':860,'new_queue':450,'rows':rows,'shape_counts':dict(shape),'sources':{'original2116':{'path':str(S/'completion-results.json'),'sha256':sha(S/'completion-results.json')},'new-complement':{'path':str(P/'completion-results.json'),'sha256':sha(P/'completion-results.json')}},'scope':'Only COMPLETE records provide exhaustive source coverage; UNKNOWN/unvisited remain unresolved. Completeness rests on unchanged accepted2116 search-code audit, not independent enumeration replay.'}
(P/'coverage-map.json').write_text(json.dumps(coverage,indent=2)+'\n')
result={'status':'PASS_SAVED_GRAPHS_AND_CODE_AUDIT','new_visited':len(new['results']),'new_counts':dict(counts),'saved_graphs_checked':ngraph,'shape_counts':dict(shape),'seconds':time.monotonic()-start,'scope':coverage['scope']}
(P/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
