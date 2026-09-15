import hashlib
import itertools
import json
from pathlib import Path
OLD=Path('/Users/rwalters/lean-genius-h7-f0-sol1-20260915')

def load():
    launch=json.loads((OLD/'high-launch.json').read_text())
    source=Path(launch['source_path'])
    for name,h in launch['source_pins'].items():assert hashlib.sha256((source/name).read_bytes()).hexdigest()==h
    cover=json.loads((source/'results.json').read_text())
    done=json.loads((source/'completion-results.json').read_text())
    records=[r for r in done['results'] if r['F_index']==0]
    assert len(records)==48 and all(r['status']=='COMPLETE' for r in records)
    cases=[(r['source_index'],j,es) for r in records for j,es in enumerate(r['solutions'])]
    high=json.loads((OLD/'high-results.json').read_text())['results']
    assert len(cases)==len(high)==2020
    assert sum(len(r['pairings']) for r in high)==18408
    for ci,(case,r) in enumerate(zip(cases,high)):
        assert (r['case_index'],r['source_index'],r['singleton_index'])==(ci,case[0],case[1])
    return cover,cases,high

def graph(cover,cases,high,ci,pi):
    si,sj,es=cases[ci];rep=cover['representatives'][si];assert rep['F_index']==0
    g=[set() for _ in range(49)]
    def add(u,v):g[u].add(v);g[v].add(u)
    def ren(v):return v+42 if v<7 else v
    for u,v in rep['F_edges']+es:add(ren(u),ren(v))
    for s,hs in enumerate(rep['singleton_hosts'],7):
        for e in hs:add(s,42+e)
    for p,(u,v) in enumerate(itertools.combinations(range(7),2),21):add(p,u);add(p,v)
    for h,d in enumerate(high[ci]['pairings'][pi]):add(h,14+h);add(h,7+d)
    return g
