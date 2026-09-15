"""Check the exact immutable prefix/suffix union for the F2 closure."""
import collections
import gzip
import hashlib
import itertools
import json
from pathlib import Path

P=Path(__file__).parent
old=json.loads((P/'residual/results.json').read_text())
new=json.loads((P/'finish/results.json').read_text())
assert old['retained']==[[3710,1,9,'UNKNOWN']]
assert old['visited']==705876 and old['unvisited']==79532
assert new['total']==new['visited']==79533 and new['unvisited']==0 and not new['retained']
assert set(new['counts'])<= {'INFEASIBLE_ROW','INFEASIBLE_ARC'}
cut=old['visited']-1
offset=selected=0
with gzip.open(P/'finish/source-leaves.jsonl.gz','rt') as source:
    for line in gzip.open(P/'residual/source-leaves.jsonl.gz','rt'):
        full=json.loads(line);n=len(full['hosts']);first=max(0,cut-offset)
        if first<n:
            part=json.loads(next(source))
            assert part['case_index']==full['case_index'] and part['pairing_index']==full['pairing_index']
            assert part['first_leaf']==first and part['hosts']==full['hosts'][first:]
            if selected==0: assert [part['case_index'],part['pairing_index'],first]==old['retained'][0][:3]
            selected+=len(part['hosts'])
        offset+=n
    assert next(source,None) is None
assert offset==785408 and selected==79533 and cut+selected==offset
for stage in ('residual','finish'):
    summary=json.loads((P/stage/'results.json').read_text())
    verification=json.loads((P/stage/'verification.json').read_text())
    assert verification['status']=='PASS_NEGATIVE_RECEIPTS'
    assert verification['counts']==summary['counts'] and verification['visited']==summary['visited']
totals=collections.Counter(old['counts'])+collections.Counter(new['counts'])
del totals['UNKNOWN']
assert dict(totals)=={'INFEASIBLE_ROW':784344,'INFEASIBLE_ARC':1064}
assert sum(totals.values())==offset
mapping=json.loads((P/'f2-root-mapping.json').read_text())
entry=mapping['matches'][0]
assert entry['root']['id']=='cube_F7_t2' and entry['root']['mask']==328007
edges=[e for i,e in enumerate(itertools.combinations(range(7),2)) if 328007>>i&1]
assert [list(e) for e in edges]==mapping['target_edges']
result={'status':'PASS_EXACT_UNION','host_leaves':offset,'original_negative_prefix':cut,
        'finishing_slice':selected,'counts':dict(totals),'unresolved':0,'root':'cube_F7_t2',
        'scope':'Exact computational closure join, conditional on accepted source-cover and negative-endpoint reviews. No Lean or H7/global exclusion.'}
(P/'merge-verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
