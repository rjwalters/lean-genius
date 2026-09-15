"""Exact two-row overlay after accepted F0 and F6 graph exclusions."""
import copy,hashlib,itertools,json
from pathlib import Path
P=Path(__file__).parent
read=lambda n:json.loads((P/n).read_text())
p=read('provenance.json')
for name,meta in p['inputs'].items():assert hashlib.sha256((P/name).read_bytes()).hexdigest()==meta['sha256']
old=read('previous-map.json');assert old['counts']=={'total':28,'covered':15,'residual':13}
assert len({r['id'] for r in old['rows']})==28
rows=copy.deepcopy(old['rows']);added=[]
for f,mask in [(0,139591),(6,622663)]:
 rid=p['closure_reviews'][str(f)]
 review=read(f'review-{rid}.json');mapping=read(f'f{f}-root-mapping.json')
 assert review['id']==rid and review['status']=='resolved' and review['resolution'].startswith(f'PASS whole F{f}')
 target=next(r for r in rows if r['id']==f'cube_F7_t{f}')
 assert target['id'] in old['residual'] and target['mask']==mask
 if f==0:
  assert mapping['root']==target;edges=mapping['edges'];perm=mapping['parent_to_F0']
 else:
  assert len(mapping['matches'])==1 and mapping['matches'][0]['root']==target
  edges=mapping['target_edges'];perm=mapping['matches'][0]['parent_to_F6']
 assert edges==[list(e) for i,e in enumerate(itertools.combinations(range(7),2)) if mask>>i&1]
 assert perm==list(range(7))
 target.update(scope=f'F{f}',review_id=rid,parent_to_reviewed_shape=perm,status='COVERED_BY_SELECTED_REVIEWED_STRUCTURAL_SCOPE')
 added.append(target['id'])
covered=[r['id'] for r in rows if r['id'] in set(old['covered'])|set(added)]
remaining=[r['id'] for r in rows if r['id'] not in covered]
assert len(covered)==17 and len(remaining)==11
assert set(old['residual'])-set(remaining)==set(added)
for a,b in zip(old['rows'],rows):
 if a['id'] not in added:assert a==b
assert sum(x.startswith('cube_F6_') for x in remaining)==6
assert sum(x.startswith('cube_F7_') for x in remaining)==5
result={'status':'PASS_REVIEWED_SCOPE_OVERLAY','source_revision':p['revision'],'rows':rows,'covered':covered,'residual':remaining,'newly_covered':added,'counts':{'total':28,'covered':17,'residual':11},'scope':'Selected reviewed finite structural graph exclusions at paper/computation level; upstream source completeness code-audit premises retained. No Lean/kernel closure, arbitrary CNF UNSAT, whole H7 or Erdős85 proof.'}
s=json.dumps(result,indent=2)+'\n'
if (P/'results.json').exists():assert (P/'results.json').read_text()==s
else:(P/'results.json').write_text(s)
print(json.dumps(result['counts']))
