"""Replay the independent review with only its historical input path relocated."""
from pathlib import Path
import hashlib,json,tempfile
P=Path(__file__).resolve().parent
for name in ['source','review']:
 for f,h in json.loads((P/name/'pins.json').read_text()).items():
  assert hashlib.sha256((P/name/f).read_bytes()).hexdigest()==h,(name,f)
reviews=json.loads((P/'reviews.json').read_text())
assert {r['id'] for r in reviews}=={2090,2091}
assert all(r['status']=='resolved' and r['resolution'].startswith('PASS') for r in reviews)
source=(P/'review/check.py').read_text()
old="pathlib.Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/h7-a7-singleton-core')"
assert source.count(old)==1
source=source.replace(old,repr(str(P/'source')))
source=source.replace('S='+repr(str(P/'source')), 'S=pathlib.Path('+repr(str(P/'source'))+')',1)
with tempfile.TemporaryDirectory(prefix='h7-a7-core-review-') as tmp:
 env={'__file__':str(Path(tmp)/'check.py'),'__name__':'__main__'}
 exec(compile(source,str(P/'review/check.py'),'exec'),env)
 actual=json.loads((Path(tmp)/'results.json').read_text())
 expected=json.loads((P/'review/results.json').read_text())
 for key in expected:
  if key!='seconds':assert actual[key]==expected[key],key
print('PASS: portable independent core-cover and colour-count replay; reviews2090/2091 accepted.')
