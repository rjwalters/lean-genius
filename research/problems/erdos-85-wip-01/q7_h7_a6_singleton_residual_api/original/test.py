import collections,json,pathlib,time
import native,reference
P=pathlib.Path(__file__).parent
fixtures=json.loads((P/'fixtures.json').read_text());comparisons=0;expired=0;invalid=0;rows=[]
for i,g in enumerate(fixtures):
    terminal=reference.check(g)
    caps=sorted({0,1,2,35,terminal['nodes']//2,terminal['nodes']-1,terminal['nodes'],100000})
    for cap in caps:
        assert native.check(g,max_nodes=cap)==reference.check(g,max_nodes=cap),(i,cap)
        comparisons+=1
    assert native.check(g,deadline=time.monotonic()-1)==reference.check(g,deadline=time.monotonic()-1);expired+=1
    rows.append(dict(index=i,status=terminal['status'],nodes=terminal['nodes']))
    for api in [native,reference]:
        for cap in [-1,1.5]:
            try:api.check(g,max_nodes=cap);raise AssertionError('bad cap accepted')
            except ValueError:invalid+=1
        bad=[list(ns) for ns in g];bad[0].append(0)
        try:api.check(bad);raise AssertionError('selfloop accepted')
        except ValueError:invalid+=1
timings={}
for name,api in [('python',reference),('native',native)]:
    t=time.monotonic()
    for g in fixtures:api.check(g)
    timings[name]=time.monotonic()-t
result=dict(status='PASS',fixtures=len(fixtures),comparisons=comparisons,expired=expired,invalid_rejections=invalid,timings=timings,results=rows)
(P/'results.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items() if k!='results'})
