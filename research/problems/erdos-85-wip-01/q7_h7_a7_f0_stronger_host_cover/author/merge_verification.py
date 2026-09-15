import collections
import json
from pathlib import Path
P=Path(__file__).parent
result=json.loads((P/'results.json').read_text())
parts=[json.loads((P/f'verification-part-{i}.json').read_text()) for i in range(4)]
counts=collections.Counter()
for i,p in enumerate(parts):
    assert p['status']=='PASS_PART' and p['part']==i and p['parts']==4
    assert p['visited']==result['visited'] and p['selected']==len(range(i,result['visited'],4))
    counts.update(p['counts'])
assert sum(p['selected'] for p in parts)==result['visited'] and dict(counts)==result['counts']
for field,target in [('negative_high_inputs','negative_high_inputs'),('leaves','surviving_host_leaves'),
                     ('pair_prunes','pair_prunes_complete'),('singleton_prunes','singleton_prunes_complete')]:
    assert sum(p[field] for p in parts)==result[target]
assert result['unvisited']==0 and result['counts']=={'COMPLETE':18340}
out={'status':'PASS_COMPLETE_COVER','new_inputs':18340,'inherited_negative_inputs':68,'total_high_inputs':18408,
     'new_negative_inputs':result['negative_high_inputs'],'leaves':result['surviving_host_leaves'],
     'pair_prunes':result['pair_prunes_complete'],'singleton_prunes':result['singleton_prunes_complete'],
     'max_worker_seconds':max(p['seconds'] for p in parts),'partition':'queue-index mod4, exhaustive and disjoint',
     'scope':'Complete necessary stronger-host cover with all endpoints checked; 3012 leaves still require residual exclusion.'}
(P/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
