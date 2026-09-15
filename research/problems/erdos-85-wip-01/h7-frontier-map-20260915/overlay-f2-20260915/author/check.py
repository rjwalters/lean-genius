"""Reproduce the selected H7 scope overlay from immutable reviewed inputs."""
import copy
import hashlib
import itertools
import json
from pathlib import Path

P=Path(__file__).parent
provenance=json.loads((P/'provenance.json').read_text())
for name,meta in provenance['inputs'].items():
    assert hashlib.sha256((P/name).read_bytes()).hexdigest()==meta['sha256']
old=json.loads((P/'historical-map.json').read_text())
review=json.loads((P/'review-2659.json').read_text())
mapping=json.loads((P/'f2-root-mapping.json').read_text())
assert old['counts']=={'total':28,'covered':12,'residual':16}
assert review['id']==2659 and review['status']=='resolved' and review['resolution'].startswith('PASS whole F2')
assert len({r['id'] for r in old['rows']})==28
rows=copy.deepcopy(old['rows'])
target=next(r for r in rows if r['id']=='cube_F7_t2')
assert target in [x['root'] for x in mapping['matches']]
assert target['mask']==328007 and target['id'] in old['residual']
edges=[list(e) for i,e in enumerate(itertools.combinations(range(7),2)) if target['mask']>>i&1]
assert edges==mapping['target_edges']==[[0,1],[0,2],[0,3],[1,2],[1,4],[3,5],[4,5]]
target.update(scope='F2',review_id=2659,parent_to_reviewed_shape=list(range(7)),
              status='COVERED_BY_SELECTED_REVIEWED_STRUCTURAL_SCOPE')
covered=[r['id'] for r in rows if r['id'] in set(old['covered'])|{'cube_F7_t2'}]
remaining=[r['id'] for r in rows if r['id'] not in covered]
assert len(covered)==13 and len(remaining)==15
assert set(old['residual'])-set(remaining)=={'cube_F7_t2'}
for a,b in zip(old['rows'],rows):
    if a['id']!='cube_F7_t2':assert a==b
result={'status':'PASS_REVIEWED_SCOPE_OVERLAY','source_revision':provenance['revision'],
        'rows':rows,'covered':covered,'residual':remaining,
        'counts':{'total':28,'covered':13,'residual':15},
        'newly_covered':['cube_F7_t2'],
        'scope':'Selected reviewed structural graph exclusions at paper/computation level. Historical map preserved. No Lean kernel closure or arbitrary CNF UNSAT; fifteen roots remain outside selected scopes.'}
text=json.dumps(result,indent=2)+'\n'
out=P/'results.json'
if out.exists():assert out.read_text()==text
else:out.write_text(text)
print(json.dumps(result['counts']))
