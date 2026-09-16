"""claude: one-row H7 scope overlay 27 -> 28 (a6 F14 / cube_F6_t18, review 2718). Own implementation."""
import copy,hashlib,itertools,json
from pathlib import Path
P=Path(__file__).parent
read=lambda n:json.loads((P/n).read_text())
prov=read('provenance.json')
for name,meta in prov['inputs'].items():
    assert hashlib.sha256((P/name).read_bytes()).hexdigest()==meta['sha256'],name
old=read('previous-map.json')
assert old['status']=='PASS_REVIEWED_SCOPE_OVERLAY' and old['counts']=={'total':28,'covered':27,'residual':1} and old['residual']==['cube_F6_t18']
assert len(old['rows'])==28 and len({r['id'] for r in old['rows']})==28
rows=copy.deepcopy(old['rows'])
target=next(r for r in rows if r['id']=='cube_F6_t18')
assert target['status']=='NOT_COVERED_BY_SELECTED_SCOPES' and target['mask']==594051 and target['edge_count']==6
m=read('f14-map.json')
assert m['root']==target and m['source_F_index']==14
perm=m['parent_to_source']; assert sorted(perm)==list(range(7))
pairs=list(itertools.combinations(range(7),2))
root_edges=[pairs[i] for i in range(21) if target['mask']>>i&1]
assert len(root_edges)==6 and bin(target['mask']).count('1')==6
assert {tuple(sorted((perm[u],perm[v]))) for u,v in root_edges}=={tuple(e) for e in m['source_edges']}
q=read('review-2718.json')
assert q['id']==2718 and q['status']=='resolved' and q['requested_by']=='codex-sol-2' and q['resolved_by']=='codex-sol-1'
assert q['resolution'].startswith('PASS whole a6 F14 necessary structural graph-cover exclusion, cube_F6_t18 mask594051')
target.update(scope='F14',review_id=2718,parent_to_reviewed_shape=perm,status='COVERED_BY_SELECTED_REVIEWED_STRUCTURAL_SCOPE')
for a,b in zip(old['rows'],rows):
    if a['id']!='cube_F6_t18': assert a==b
    else:
        for k in ('id','edge_count','mask','cnf_sha256'): assert a[k]==b[k]
covered=[r['id'] for r in rows if r['status']=='COVERED_BY_SELECTED_REVIEWED_STRUCTURAL_SCOPE' or r['id'] in old['covered']]
assert len(covered)==28 and set(covered)=={r['id'] for r in rows}
out={'status':'PASS_REVIEWED_SCOPE_OVERLAY','source_revision':prov['revision'],'rows':rows,'covered':covered,'residual':[],'newly_covered':['cube_F6_t18'],
     'counts':{'total':28,'covered':28,'residual':0},
     'scope':'All 28 frozen H7 roots lie in selected necessary structural graph exclusions reviewed at paper+computation level; source/quotient completeness (2116 a7 enumerator audit, 2118/2122/2125/2133 a6) inherited. No arbitrary CNF UNSAT, no Lean/kernel theorem, no H1, no global Erdős 85 proof.'}
s=json.dumps(out,indent=2)+'\n'
if (P/'results.json').exists(): assert (P/'results.json').read_text()==s
else: (P/'results.json').write_text(s)
print(json.dumps(out['counts']))
