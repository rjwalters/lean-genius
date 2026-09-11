from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
for name in ['source','review']:
 for f,h in json.loads((p/name/'pins.json').read_text()).items():
  assert hashlib.sha256((p/name/f).read_bytes()).hexdigest()==h,(name,f)
r=json.loads((p/'review-record.json').read_text())
assert r['id']==2093 and r['status']=='resolved' and r['resolution'].startswith('PASS')
s=json.loads((p/'source/summary.json').read_text());c=json.loads((p/'source/census-results.json').read_text());v=json.loads((p/'source/verification.json').read_text())
assert s['total']==s['visited']==3780 and s['unvisited']==0
assert s['counts']=={'INFEASIBLE_ARC':3379,'INFEASIBLE_LOCAL':401}
assert c['status']=='COMPLETE' and c['raw_count']==c['disjoint_orbit_union']==15120 and c['source_representatives']==3780
assert v['verified']==3780 and v['unvisited']==0
print('PASS: archive hashes, complete-domain counts, and accepted review2093. Row enumeration was not rerun.')
