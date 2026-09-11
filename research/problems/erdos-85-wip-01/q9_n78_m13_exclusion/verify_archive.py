from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
for f,h in json.loads((p/'archive-pins.json').read_text()).items():
 assert hashlib.sha256((p/f).read_bytes()).hexdigest()==h,f
records=json.loads((p/'review-records.json').read_text())
assert {r['id'] for r in records}=={2140,2153,2161,2162}
assert all(r['status']=='resolved' and r['resolution'].startswith('PASS') for r in records)
print('PASS archive hashes and exact accepted closure premises; no research rerun')
