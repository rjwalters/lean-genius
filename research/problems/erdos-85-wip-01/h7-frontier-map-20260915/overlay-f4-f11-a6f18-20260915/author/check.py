import copy,hashlib,itertools,json
from pathlib import Path
P=Path(__file__).parent
read=lambda n:json.loads((P/n).read_text())
p=read('provenance.json')
for n,m in p['inputs'].items():assert hashlib.sha256((P/n).read_bytes()).hexdigest()==m['sha256']
old=read('previous-map.json');assert old['counts']=={'total':28,'covered':18,'residual':10}
rows=copy.deepcopy(old['rows']);assert len({r['id'] for r in rows})==28
cases=[('cube_F7_t4','F4',2690,1114439,'f4-map.json','PASS whole F4'),('cube_F7_t11','F11',2689,401671,'f11-map.json','PASS whole F11'),('cube_F6_t16','F18',2692,1085571,'a6f18-map.json','PASS whole a6 F18')]
added=[]
for rid,scope,review_id,mask,name,prefix in cases:
 r=next(r for r in rows if r['id']==rid);assert rid in old['residual'] and r['mask']==mask
 review=read(f'review-{review_id}.json');assert review['id']==review_id and review['status']=='resolved' and review['resolution'].startswith(prefix)
 m=read(name)
 if scope=='F18':assert m['root']==r;perm=m['parent_to_source'];target=m['source_edges'];assert m['source_F_index']==18
 else:
  assert len(m['matches'])==1 and m['matches'][0]['root']==r
  perm=m['matches'][0]['parent_to_'+scope];target=m['target_edges']
 assert sorted(perm)==list(range(7))
 edges=[e for i,e in enumerate(itertools.combinations(range(7),2)) if mask>>i&1]
 assert {tuple(sorted((perm[u],perm[v]))) for u,v in edges}==set(map(tuple,target))
 r.update(scope=scope,review_id=review_id,parent_to_reviewed_shape=perm,status='COVERED_BY_SELECTED_REVIEWED_STRUCTURAL_SCOPE');added.append(rid)
covered=[r['id'] for r in rows if r['id'] in set(old['covered'])|set(added)];remaining=[r['id'] for r in rows if r['id'] not in covered]
assert len(covered)==21 and len(remaining)==7 and set(old['residual'])-set(remaining)==set(added)
for a,b in zip(old['rows'],rows):
 if a['id'] not in added:assert a==b
assert sum(x.startswith('cube_F6_') for x in remaining)==5 and sum(x.startswith('cube_F7_') for x in remaining)==2
out={'status':'PASS_REVIEWED_SCOPE_OVERLAY','source_revision':p['revision'],'rows':rows,'covered':covered,'residual':remaining,'newly_covered':added,'counts':{'total':28,'covered':21,'residual':7},'scope':'Selected reviewed paper/computation graph exclusions; inherited source/quotient completeness premises retained. No kernel, arbitrary CNF UNSAT, whole H7 or global Erdős85 proof.'}
s=json.dumps(out,indent=2)+'\n'
if (P/'results.json').exists():assert (P/'results.json').read_text()==s
else:(P/'results.json').write_text(s)
print(json.dumps(out['counts']))
