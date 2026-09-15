import collections,hashlib,itertools,json,time
from pathlib import Path
P=Path('/Users/rwalters/lean-genius-h7-a7-source-complement-sol2-20260915');O=Path(__file__).parent
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
l=read(P/'launch.json');S=Path(l['source']);pins={str(P/n):sha(P/n) for n in ['launch.json','complete.py','queue.json','completion-results.json']}
with (O/'launch.json').open('x') as f:json.dump({'seconds_cap':90,'inputs':pins},f,indent=2)
for n,h in l['source_pins'].items():assert sha(S/n)==h
assert l['driver_sha256']==sha(P/'complete.py') and l['max_nodes']==100000 and l['aggregate_seconds']==120
oldcode=(S/'complete.py').read_text();newcode=(P/'complete.py').read_text()
assert oldcode[oldcode.index(' base=[0]*21'):oldcode.index(' out.append(')]==newcode[newcode.index(' base=[0]*21'):newcode.index(' row=dict(')]
old=read(S/'completion-results.json');new=read(P/'completion-results.json');source=read(S/'results.json')['representatives']
known={r['source_index']:r for r in old['results'] if r['status']=='COMPLETE'}
assert set(known)==set(range(860)) and len(source)==1310
queue=read(P/'queue.json');assert queue==list(range(860,1310))
assert [r['source_index'] for r in new['results']]==queue
assert new['summary']['counts']=={'COMPLETE':450} and new['summary']['unvisited']==0
assert new['summary']['seconds']<120 and (P/'completion-results.json').stat().st_size<l['artifact_byte_cap']==100000000
start=time.monotonic();graphs=0;shape=collections.defaultdict(lambda:collections.Counter())
for r in new['results']:
    assert time.monotonic()-start<90
    i=r['source_index'];rep=source[i]
    assert r['F_index']==rep['F_index'] and r['status']=='COMPLETE' and r['nodes']<=100000
    assert r['count']==len(r['solutions'])==len({tuple(map(tuple,x)) for x in r['solutions']})
    base={tuple(sorted(e)) for e in rep['F_edges']}
    for u,ee in enumerate(rep['singleton_hosts'],7):
        for e in ee:base.add((e,u))
    targets={u:5-sum(u in e for e in base) for u in range(7,21)}
    for es in r['solutions']:
        assert all(7<=u<v<21 for u,v in es)
        edges=base|set(map(tuple,es));assert len(edges)==len(base)+len(es)
        adj=[set() for _ in range(21)]
        for u,v in edges:adj[u].add(v);adj[v].add(u)
        assert all(len(adj[u])==targets[u] for u in targets)
        # A C4 exists exactly when a pair of vertices has two distinct middle vertices.
        seen=set()
        for ns in adj:
            for pair in itertools.combinations(sorted(ns),2):
                assert pair not in seen
                seen.add(pair)
        graphs+=1
    shape[r['F_index']]['new_bases']+=1;shape[r['F_index']]['graphs']+=r['count']
assert graphs==new['summary']['solutions']==28837
for n,h in pins.items():assert sha(Path(n))==h
out={'status':'PASS_EXACT_COMPLEMENT_AND_SAVED_GRAPHS','old_complete':860,'new_complete':450,'complete_union':1310,'graphs_checked':graphs,'new_shape_counts':dict(shape),'seconds':time.monotonic()-start,'scope':'Graph outputs and exact source partition independently verified. Exhaustive S enumeration rests on byte-identical accepted2116 traversal and code audit, not independent enumeration replay.'}
(O/'REVIEW.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
