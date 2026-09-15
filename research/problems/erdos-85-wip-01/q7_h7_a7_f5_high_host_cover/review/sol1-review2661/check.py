import hashlib,itertools,json,time
from pathlib import Path
P=Path('/Users/rwalters/lean-genius-h7-f5-sol2-20260915')
O=Path(__file__).parent
def read(p):return json.loads(p.read_text())
pins=read(P/'high-pins.json')
for n,h in pins.items():assert hashlib.sha256((P/n).read_bytes()).hexdigest()==h
launch=read(P/'high-launch.json');src=Path(launch['source_path'])
for n,h in launch['source_pins'].items():assert hashlib.sha256((src/n).read_bytes()).hexdigest()==h
cover=read(src/'results.json');done=read(src/'completion-results.json')
records=[r for r in done['results'] if r['F_index']==5]
assert len(records)==28 and all(r['status']=='COMPLETE' for r in records)
assert {r['source_index'] for r in records}=={i for i,r in enumerate(cover['representatives']) if r['F_index']==5}
cases=[(r['source_index'],j,es) for r in records for j,es in enumerate(r['solutions'])]
high=read(P/'high-results.json');assert len(cases)==1500==len(high['results'])
perms=list(itertools.permutations(range(7)));start=time.monotonic();positive=total=0
for ci,((si,sj,es),r) in enumerate(zip(cases,high['results'])):
    assert time.monotonic()-start<30
    assert (r['case_index'],r['source_index'],r['singleton_index'])==(ci,si,sj) and r['status']=='COMPLETE'
    rep=cover['representatives'][si];edges=[tuple(e) for e in rep['F_edges']+es]
    edges.extend((s,e) for s,hs in enumerate(rep['singleton_hosts'],7) for e in hs)
    ns=[{b if a==v else a for a,b in edges if v in (a,b)} for v in range(21)]
    forbidden={(h,d) for h in range(7) for d in range(7) if 7+d in ns[14+h] or ns[14+h]&ns[7+d]}
    actual={p for p in perms if all((h,p[h]) not in forbidden for h in range(7))}
    saved=[tuple(p) for p in r['pairings']]
    assert len(saved)==len(set(saved)) and set(saved)==actual
    total+=len(actual);positive+=bool(actual)
assert (total,positive)==(6944,996)
out={'status':'PASS','review':2661,'cases':1500,'source_bases':28,'pairings':total,'positive':positive,
     'empty':1500-positive,'seconds':time.monotonic()-start,'method':'Independent set-neighborhood construction and all5040 permutations per source graph','scope':'High cover only.'}
(O/'REVIEW.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
