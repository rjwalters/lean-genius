from pathlib import Path
import json,hashlib
p=Path(__file__).resolve().parent;b=Path('/Users/rwalters/lean-genius-q9-known-values-20260911');src=b/'n78-normal-three-reduction';pins={}
def check(mf):
 for n,h in json.loads(mf.read_text()).items():
  f=mf.parent/n;assert hashlib.sha256(f.read_bytes()).hexdigest()==h,str(f);pins[str(f)]=h
for n in ['pins.json','input-pins.json']:check(src/n)
for n in json.loads((src/'input-pins.json').read_text()):check(Path(n))
states=json.loads((p/'premise-states.json').read_text());assert len(states)==4 and all(r['status']=='resolved' and r['resolution'].startswith('PASS') for r in states)
chars=json.loads((b/'n78-normal-three-character/results.json').read_text());assert chars['status']=='COMPLETE' and len(chars['groups'])==22
split=(3,3,12,12,12,12,24);three6=(6,6,6,12,12,12,24);six12=(6,12,12,12,12,12,12);cover=[];retained=[]
for g in chars['groups']:
 assert g['status']=='COMPLETE'
 for solution in g['solutions']:
  sizes=tuple(sorted(g['characters'][i]['values'][0] for i in solution));assert len(sizes)==7 and sum(sizes)==78
  if g['name'].startswith('E8:'):assert sizes in (split,three6)
  else:assert g['name']=='D8:01010101' and sizes in (split,six12)
  reason='2372 complete first quotient case' if sizes==split else '2371 independent paper' if sizes==six12 else 'remaining geometry2374'
  cover.append({'group':g['name'],'character_indices':solution,'sizes':sizes,'disposition':reason})
  if sizes==three6:retained.append(g['name'])
assert len(cover)==37 and len(set(retained))==7 and all(x.startswith('E8:') for x in retained)
q=json.loads((b/'n78-normal-three-quotients/results.json').read_text());assert q['status']=='INCOMPLETE'
first,second,third=q['cases'];assert tuple(first['sizes'])==split and first['status']=='COMPLETE' and not first['quotients']
assert second['status']=='COMPLETE' and third['status']=='UNKNOWN'
result={'status':'PASS','verified_payloads':len(pins),'fresh_pass_reviews':4,'character_solutions_classified':len(cover),'remaining_labelled_groups':sorted(set(retained)),'original_quotient_status':q['status'],'third_quotient_status':third['status'],'coverage':cover}
(p/'verification.json').write_text(json.dumps(result,indent=2)+'\n');(p/'input-pins.json').write_text(json.dumps(pins,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='coverage'}))
