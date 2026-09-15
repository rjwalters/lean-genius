"""Reproduce the reviewed F3/F5 scope overlay without any search or replay."""
import copy,hashlib,itertools,json
from pathlib import Path
P=Path(__file__).parent
def read(n):return json.loads((P/n).read_text())
provenance=read('provenance.json')
for name,meta in provenance['inputs'].items():
    assert hashlib.sha256((P/name).read_bytes()).hexdigest()==meta['sha256']
old=read('previous-map.json');assert old['counts']=={'total':28,'covered':13,'residual':15}
assert len({r['id'] for r in old['rows']})==28
rows=copy.deepcopy(old['rows']);added=[]
for f,rid,mask in [(3,2667,590151),(5,2665,360519)]:
    review=read(f'review-{rid}.json');mapping=read(f'f{f}-root-mapping.json')
    assert review['id']==rid and review['status']=='resolved' and review['resolution'].startswith(f'PASS whole F{f}')
    target=next(r for r in rows if r['id']==f'cube_F7_t{f}')
    assert target['id'] in old['residual'] and target['mask']==mask
    assert mapping['matches'][0]['root']==target
    edges=[list(e) for i,e in enumerate(itertools.combinations(range(7),2)) if mask>>i&1]
    assert edges==mapping['target_edges']
    assert mapping['matches'][0][f'parent_to_F{f}']==list(range(7))
    target.update(scope=f'F{f}',review_id=rid,parent_to_reviewed_shape=list(range(7)),
                  status='COVERED_BY_SELECTED_REVIEWED_STRUCTURAL_SCOPE')
    added.append(target['id'])
covered=[r['id'] for r in rows if r['id'] in set(old['covered'])|set(added)]
remaining=[r['id'] for r in rows if r['id'] not in covered]
assert len(covered)==15 and len(remaining)==13
assert set(old['residual'])-set(remaining)==set(added)
for a,b in zip(old['rows'],rows):
    if a['id'] not in added:assert a==b
assert sum(x.startswith('cube_F6_') for x in remaining)==6
assert sum(x.startswith('cube_F7_') for x in remaining)==7
result={'status':'PASS_REVIEWED_SCOPE_OVERLAY','source_revision':provenance['revision'],
        'rows':rows,'covered':covered,'residual':remaining,'newly_covered':added,
        'counts':{'total':28,'covered':15,'residual':13},
        'scope':'Selected reviewed structural graph exclusions at paper/computation level; no Lean kernel closure, arbitrary CNF UNSAT, or whole H7/Erdos85 proof.'}
out=P/'results.json';text=json.dumps(result,indent=2)+'\n'
if out.exists():assert out.read_text()==text
else:out.write_text(text)
print(json.dumps(result['counts']))
