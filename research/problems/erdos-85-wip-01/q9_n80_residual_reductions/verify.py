from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
pins=json.loads((p/'manifest.json').read_text())
for name,h in pins.items():
 q=p/name
 assert q.is_file(),name
 assert hashlib.sha256(q.read_bytes()).hexdigest()==h,name
actual={str(q.relative_to(p)) for q in p.rglob('*') if q.is_file() and q.name!='manifest.json' and '__pycache__' not in q.parts}
assert actual==set(pins), 'Unexpected or missing payload'
print(f'PASS {len(pins)} payload hashes')
