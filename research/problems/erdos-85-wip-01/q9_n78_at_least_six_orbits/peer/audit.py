from pathlib import Path
import json,hashlib
out=Path(__file__).resolve().parent;src=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n78-at-least-six-orbits');base=src.parent
pins={}
def check_manifest(p):
 for n,h in json.loads(p.read_text()).items():
  f=p.parent/n
  assert hashlib.sha256(f.read_bytes()).hexdigest()==h,str(f)
  pins[str(f)]=h
for name in ['pins.json','input-pins.json']:check_manifest(src/name)
for f in json.loads((src/'input-pins.json').read_text()):check_manifest(Path(f))
states=json.loads((out/'premise-states.json').read_text());assert len(states)==13
assert all(r['status']=='resolved' and r['resolution'].startswith('PASS') for r in states)
q=json.loads(Path('/tmp/erdos85-sol1-q9-n78-five-orbit-quotients/results.json').read_text());assert q['status']=='COMPLETE'
cover=[]
for case in q['cases']:
 assert case['status']=='COMPLETE'
 ns=case['sizes'];qs=[m for m in case['quotients'] if all(ns[i]*m[i][i]%2==0 for i in range(5))]
 if 8 in ns:kind='excluded by accepted Sylow3 incidence'
 elif not qs:kind='no parity-valid quotient'
 elif ns==[3,3,24,24,24]:
  assert case['order']==24 and len(qs)==6
  for m in qs:assert m[0][1]==m[1][0]==1 and m[0][0]==m[1][1]==0
  kind='split centers'
 else:
  assert ns==[6,12,12,24,24] and case['order'] in [24,48]
  single=[m for m in qs if m[0]==[1,0,0,4,4]];double=[m for m in qs if m not in single]
  assert len(single)==8 and len(double)==4
  for m in single:
   assert m[3][3]==m[4][4] and m[3][3] in range(1,5) and m[3][4]==5-m[3][3]
   assert sorted([m[1][3],m[1][4]])==[2,4] and sorted([m[2][3],m[2][4]])==[2,4]
  for m in double:assert m[0][0]==1 and sorted(m[0][1:3])==[0,4] and sorted(m[0][3:])==[0,4]
  kind='order48 exclusion' if case['order']==48 else 'eight single and four double'
 cover.append({'order':case['order'],'sizes':ns,'parity_valid':len(qs),'disposition':kind})
cross=json.loads((base/'n78-five-orbit-single-cross/results.json').read_text());first=json.loads((base/'n78-five-orbit-single-residual/results.json').read_text());second=json.loads((base/'n78-five-orbit-single-second-residual/results.json').read_text())
for d in (cross,first,second):assert d['status']=='COMPLETE' and all(r['status']=='COMPLETE' for r in d['records'])
e1={(i,j) for i,r in enumerate(cross['records']) for j in range(len(r['survivors']))};a1=[(r['root'],r['configuration']) for r in first['records']];assert len(a1)==len(set(a1))==12928 and set(a1)==e1
e2={(i,j) for i,r in enumerate(first['records']) for j in range(len(r['survivors']))};a2=[(r['first_record'],r['first_solution']) for r in second['records']];assert len(a2)==len(set(a2))==896 and set(a2)==e2
assert all(not r['survivors'] for r in second['records'])
result={'status':'PASS','verified_payloads':len(pins),'fresh_pass_reviews':13,'five_orbit_cover':cover,'first_filter_inputs':12928,'second_filter_inputs':896,'second_survivors':0}
(out/'verification.json').write_text(json.dumps(result,indent=2)+'\n');(out/'input-pins.json').write_text(json.dumps(pins,indent=2)+'\n');print(json.dumps(result))
