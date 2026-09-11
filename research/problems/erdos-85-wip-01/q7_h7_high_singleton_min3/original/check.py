from pathlib import Path
import json,hashlib
p=Path(__file__).parent;profiles=json.loads((p/'profile-source.json').read_text())['results'];reviews={r['id']:r for r in json.loads((p/'reviews.json').read_text())};endpoints=json.loads((p/'endpoints.json').read_text())
assert all(r['status']=='resolved' and r['resolution'].startswith('PASS') for r in reviews.values())
keys=[]
for family in profiles:
 for i,row in enumerate(family['representatives']):
  if sum(row['empty_counts'][:2])<=2:keys.append((family['twins_adjacent'],i))
assert len(keys)==9 and set(keys)=={(r['twins_adjacent'],r['profile_index']) for r in endpoints} and len(endpoints)==9
assert all(all(i in reviews for i in r['reviews']) for r in endpoints)
cases=[]
for a in [6,7,8,9]:
 total=49-4*a
 if total<21:cases.append({'a':a,'status':'EXCLUDED','singleton_empty_incidence':total,'required_minimum':21})
 else:
  four=total-21;three=7-four;assert 0<=four<=7
  cases.append({'a':a,'status':'NECESSARY_STRUCTURE','highs_with_singleton_sum_4':four,'highs_with_singleton_sum_3':three,'complement_degree_3':four,'complement_degree_2':three})
cycles=json.loads((p/'cycle-results.json').read_text());assert cycles['status']=='PASS' and cycles['labelled_2regular_graphs']==465 and cycles['cycle_type_counts']=={'(3, 4)':105,'(7,)':360}
out={'status':'HIGH_SINGLETON_MIN3_CONDITIONAL_ON_REVIEWED_GRAPH_PREMISES','excluded_small_sum_profiles':[list(k) for k in keys],'covered_assignments':sum(r['canonical_assignments'] for r in endpoints),'cases':cases,'a7_complement_types':['C7','C3 + C4'],'scope':'All highs have singleton-empty sum3or4. H7a8 excluded; a6/a7 still open. No Lean/global theorem or frozen queue change.'}
(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
