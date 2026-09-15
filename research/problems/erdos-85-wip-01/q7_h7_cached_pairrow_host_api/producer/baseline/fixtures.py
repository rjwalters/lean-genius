import gzip
import itertools
import json
from pathlib import Path

def load():
    fixtures=[]
    for f,target in [(0,8),(5,4)]:
        p=Path(f'/Users/rwalters/lean-genius-h7-f{f}-sol{1 if f==0 else 2}-20260915')
        launch=json.loads((p/'high-launch.json').read_text());source=Path(launch['source_path'])
        cover=json.loads((source/'results.json').read_text());done=json.loads((source/'completion-results.json').read_text())
        edges={(r['source_index'],j):es for r in done['results'] if r['F_index']==f for j,es in enumerate(r['solutions'])}
        high=json.loads((p/'high-results.json').read_text())['results']
        result=json.loads((p/('host-results.json' if f==0 else 'hosts/results.json')).read_text())
        shards=result['shards'] if f==0 else result['receipt_shards']
        chosen=[]
        for shard in shards:
            for line in gzip.open(p/shard if f==0 else p/'hosts'/shard,'rt'):
                r=json.loads(line)
                if f==0 and r['receipt']['status']!='UNKNOWN':continue
                if f==5 and r['case_index']%3!=0:continue
                chosen.append(r)
                if len(chosen)==target:break
            if len(chosen)==target:break
        assert len(chosen)==target
        for r in chosen:
            h=high[r['case_index']];rep=cover['representatives'][h['source_index']]
            g=[set() for _ in range(49)]
            def add(u,v):g[u].add(v);g[v].add(u)
            def ren(u):return 42+u if u<7 else u
            for u,v in rep['F_edges']+edges[h['source_index'],h['singleton_index']]:add(ren(u),ren(v))
            for s,hs in enumerate(rep['singleton_hosts'],7):
                for e in hs:add(s,42+e)
            for v,(a,b) in enumerate(itertools.combinations(range(7),2),21):add(v,a);add(v,b)
            for a,d in enumerate(h['pairings'][r['pairing_index']]):add(a,14+a);add(a,7+d)
            fixtures.append({'F_index':f,'case_index':r['case_index'],'pairing_index':r['pairing_index'],
                             'prior_status':r['receipt']['status'],'prior_nodes':r['receipt']['nodes'],
                             'adjacency':[sorted(ns) for ns in g]})
    return fixtures
