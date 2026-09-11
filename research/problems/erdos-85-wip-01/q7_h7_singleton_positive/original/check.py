from pathlib import Path
import json,hashlib
p=Path(__file__).parent;profiles=json.loads((p/'profile-source.json').read_text())['results'];reviews={r['id']:r for r in json.loads((p/'reviews.json').read_text())}
for r in reviews.values():assert r['status']=='resolved' and r['resolution'].startswith('PASS')
endpoints=json.loads((p/'endpoints.json').read_text());expected=[]
for family in profiles:
 for i,profile in enumerate(family['representatives']):
  if min(profile['empty_counts'][:2])==0:expected.append((family['twins_adjacent'],i))
assert len(expected)==6 and set(expected)=={(r['twins_adjacent'],r['profile_index']) for r in endpoints}
assert len(endpoints)==6
for r in endpoints:
 assert all(i in reviews for i in r['reviews'])
cases=[]
for a in [6,7,8]:
 z=35-4*a;l=4*a-21;assert z+l==14 and 2*z+l==49-4*a
 cases.append({'empty_edges':a,'singleton_empty_degree_2':z,'singleton_empty_degree_1':l,'singleton_empty_degree_0':0})
out={'status':'SINGLETON_POSITIVE_CONDITIONAL_ON_REVIEWED_GRAPH_PREMISES','excluded_zero_host_profiles':[list(x) for x in expected],'cases':cases,'profile_source_sha256':hashlib.sha256((p/'profile-source.json').read_bytes()).hexdigest(),'scope':'Every singleton has one or two empty neighbours in a remaining H7 graph. Six entire-profile exclusions are accepted premises; no full H7/Lean/global closure.'}
(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
