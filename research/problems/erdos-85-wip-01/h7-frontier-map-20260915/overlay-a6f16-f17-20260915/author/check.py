import copy,hashlib,itertools,json
from pathlib import Path
P=Path(__file__).parent
read=lambda n:json.loads((P/n).read_text())
p=read('provenance.json')
for n,m in p['inputs'].items():assert hashlib.sha256((P/n).read_bytes()).hexdigest()==m['sha256']
old=read('previous-map.json');assert old['counts']=={'total':28,'covered':24,'residual':4};rows=copy.deepcopy(old['rows']);added=[]
for rid,fi,review,mask in [('cube_F6_t15',16,2704,622659),('cube_F6_t5',17,2709,1081415)]:
 r=next(r for r in rows if r['id']==rid);assert rid in old['residual'] and r['mask']==mask
 m=read(f'f{fi}-map.json');assert m['root']==r and m['source_F_index']==fi;perm=m['parent_to_source'];assert sorted(perm)==list(range(7))
 edges=[e for i,e in enumerate(itertools.combinations(range(7),2)) if mask>>i&1];assert {tuple(sorted((perm[u],perm[v]))) for u,v in edges}==set(map(tuple,m['source_edges']))
 q=read(f'review-{review}.json');assert q['id']==review and q['status']=='resolved' and q['resolution'].startswith(f'PASS whole a6 F{fi}')
 r.update(scope=f'F{fi}',review_id=review,parent_to_reviewed_shape=perm,status='COVERED_BY_SELECTED_REVIEWED_STRUCTURAL_SCOPE');added.append(rid)
for a,b in zip(old['rows'],rows):
 if a['id'] not in added:assert a==b
covered=[r['id'] for r in rows if r['id'] in set(old['covered'])|set(added)];remaining=[r['id'] for r in rows if r['id'] not in covered]
assert len(covered)==26 and set(remaining)=={'cube_F6_t17','cube_F6_t18'}
out={'status':'PASS_REVIEWED_SCOPE_OVERLAY','source_revision':p['revision'],'rows':rows,'covered':covered,'residual':remaining,'newly_covered':added,'counts':{'total':28,'covered':26,'residual':2},'scope':'Selected necessary structural graph exclusions; source/quotient completeness inherited. No arbitrary CNF UNSAT, kernel, wholeH7 or global proof.'}
s=json.dumps(out,indent=2)+'\n'
if (P/'results.json').exists():assert (P/'results.json').read_text()==s
else:(P/'results.json').write_text(s)
print(json.dumps(out['counts']))
