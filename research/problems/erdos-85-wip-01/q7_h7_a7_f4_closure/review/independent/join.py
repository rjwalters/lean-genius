"""Independent exact F4 host-export join, without invoking any producer."""
import gzip
import hashlib
import itertools
import json
import time
from pathlib import Path
P=Path('/Users/rwalters/lean-genius-h7-f4-sol1-20260915')
D=Path(__file__).parent
start=time.monotonic()
host=json.loads((P/'hosts/results.json').read_text())
count=groups=0
with gzip.open(P/'residual/source-leaves.jsonl.gz','rt') as source:
    for shard in host['receipt_shards']:
        for line in gzip.open(P/'hosts'/shard,'rt'):
            assert time.monotonic()-start<120,'Join audit cap'
            r=json.loads(line);assert r['receipt']['status']=='COMPLETE'
            hs=r['receipt']['solutions']
            if not hs: continue
            export=json.loads(next(source))
            assert (r['case_index'],r['pairing_index'])==(export['case_index'],export['pairing_index'])
            assert hs==[[m<<21 for m in masks] for masks in export['hosts']]
            count+=len(hs);groups+=1
    assert next(source,None) is None
assert count==host['surviving_host_leaves_complete']==1643512
mapping=json.loads((P/'f4-root-mapping.json').read_text())
edges=[list(e) for i,e in enumerate(itertools.combinations(range(7),2)) if 1114439>>i&1]
assert edges==[[0,1],[0,2],[0,3],[1,2],[1,4],[3,5],[5,6]]
assert mapping['target_edges']==edges and mapping['matches'][0]['root']['id']=='cube_F7_t4'
result={'status':'PASS_EXACT_HOST_EXPORT','leaves':count,'positive_groups':groups,'root':'cube_F7_t4',
        'seconds':time.monotonic()-start,'scope':'Exact source masks/order and root identity only; endpoint verification separate.'}
(D/'join-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
