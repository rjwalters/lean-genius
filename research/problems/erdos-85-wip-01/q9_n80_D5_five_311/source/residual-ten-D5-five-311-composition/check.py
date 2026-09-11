"""Composition bookkeeping; relies on the separately reviewed mathematical stages."""
import json, hashlib
from pathlib import Path
P=Path(__file__).resolve().parent
reviews=json.loads((P/'reviews.json').read_text())
checked={}
def pins(path):
    path=Path(path)
    for name,expected in json.loads(path.read_text()).items():
        target=Path(name)
        if not target.is_absolute(): target=path.parent/target
        actual=hashlib.sha256(target.read_bytes()).hexdigest()
        assert actual==expected,(str(target),expected,actual)
        checked[str(target)]=actual
        if target.name=='input-pins.json': pins(target)
for review in reviews:
    for ref in review['refs']: pins(ref)
def data(name):
    return json.loads((P.parent/('residual-ten-D5-five-311-'+name)/'results.json').read_text())
a=data('full-center-configurations'); b=data('centered-propagation')
assert a['status']==b['status']=='COMPLETE'
assert len(a['records'])==len(b['records'])==29
assert {r['root'] for r in a['records']}=={r['root'] for r in b['records']}
expected={(r['root'],c['high_assignment'],i) for r in a['records'] for c in r['configs'] for i,_ in enumerate(c['survivors'])}
actual=[]
for r in b['records']:
    assert r['status']=='COMPLETE'
    for c in r['records']:
        assert c['status']=='NEGATIVE'
        actual.append((r['root'],c['high_assignment'],c['center_config']))
assert len(actual)==len(set(actual))==len(expected)==706
assert set(actual)==expected
pending=[r['id'] for r in reviews if r['status']!='resolved' or not (r.get('resolution') or '').startswith('PASS')]
result={'status':'CONDITIONAL_PENDING_REVIEW' if pending else 'DEPENDENCIES_ACCEPTED_COMPOSITION_REVIEW_REQUIRED','pending_reviews':pending,'checked_hashes':len(checked),'exact_center_configurations':len(expected),'all_negative':True,'scope':'D5, five 311 groups only; no global or Lean claim'}
(P/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
(P/'source-hashes.json').write_text(json.dumps(checked,indent=2)+'\n')
print(json.dumps(result))
