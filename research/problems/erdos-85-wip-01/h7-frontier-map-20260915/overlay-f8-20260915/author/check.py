import json,hashlib,copy,itertools
from pathlib import Path
P=Path(__file__).parent
read=lambda n:json.loads((P/n).read_text())
p=read('provenance.json')
for n,m in p['inputs'].items():assert hashlib.sha256((P/n).read_bytes()).hexdigest()==m['sha256']
old=read('previous-map.json');assert old['counts']=={'total':28,'covered':17,'residual':11}
rows=copy.deepcopy(old['rows']);assert len({r['id'] for r in rows})==28
r=next(r for r in rows if r['id']=='cube_F7_t8');assert r['id'] in old['residual'] and r['mask']==1343559
m=read('f8-root-mapping.json');review=read('review-2681.json')
assert review['id']==2681 and review['status']=='resolved' and review['resolution'].startswith('PASS whole F8')
assert len(m['matches'])==1 and m['matches'][0]['root']==r and m['matches'][0]['parent_to_F8']==list(range(7))
assert m['target_edges']==[list(e) for i,e in enumerate(itertools.combinations(range(7),2)) if 1343559>>i&1]
r.update(scope='F8',review_id=2681,parent_to_reviewed_shape=list(range(7)),status='COVERED_BY_SELECTED_REVIEWED_STRUCTURAL_SCOPE')
added=['cube_F7_t8'];covered=[r['id'] for r in rows if r['id'] in set(old['covered'])|set(added)];remaining=[r['id'] for r in rows if r['id'] not in covered]
assert len(covered)==18 and len(remaining)==10 and set(old['residual'])-set(remaining)==set(added)
for a,b in zip(old['rows'],rows):
 if a['id'] not in added:assert a==b
assert sum(x.startswith('cube_F6_') for x in remaining)==6 and sum(x.startswith('cube_F7_') for x in remaining)==4
out={'status':'PASS_REVIEWED_SCOPE_OVERLAY','source_revision':p['revision'],'rows':rows,'covered':covered,'residual':remaining,'newly_covered':added,'counts':{'total':28,'covered':18,'residual':10},'scope':'Selected reviewed finite structural graph exclusions only; upstream source-code completeness premises retained. No Lean/kernel, arbitrary CNF UNSAT, whole H7 or global Erdős85 proof.'}
s=json.dumps(out,indent=2)+'\n'
if (P/'results.json').exists():assert (P/'results.json').read_text()==s
else:(P/'results.json').write_text(s)
print(json.dumps(out['counts']))
