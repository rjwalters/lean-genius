from pathlib import Path
import json,hashlib
p=Path(__file__).resolve().parent
for name in ['source','review']:
 for f,h in json.loads((p/name/'pins.json').read_text()).items():
  assert hashlib.sha256((p/name/f).read_bytes()).hexdigest()==h,(name,f)
r=json.loads((p/'review-record.json').read_text())
assert r['id']==2118 and r['status']=='resolved' and r['resolution'].startswith('PASS')
print('PASS archive hashes and accepted review 2118; no enumeration rerun.')
