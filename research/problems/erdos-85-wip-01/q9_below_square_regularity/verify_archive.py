from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
for f,h in json.loads((p/'archive-pins.json').read_text()).items():
 assert hashlib.sha256((p/f).read_bytes()).hexdigest()==h,f
for r in json.loads((p/'review-records.json').read_text()):
 assert r['status']=='resolved' and r['resolution'].startswith('PASS')
print('PASS archive hashes and accepted review records; no research rerun')
