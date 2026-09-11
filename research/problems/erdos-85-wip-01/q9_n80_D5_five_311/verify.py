from pathlib import Path
import json,gzip,hashlib
p=Path(__file__).resolve().parent
manifest=json.loads((p/'manifest.json').read_text())
actual={str(f.relative_to(p)) for f in p.rglob('*') if f.is_file() and f.name!='manifest.json' and '__pycache__' not in f.parts}
assert actual==set(manifest)
for f,h in manifest.items():assert hashlib.sha256((p/f).read_bytes()).hexdigest()==h,f
for logical,e in json.loads((p/'provenance.json').read_text()).items():
 data=(p/e['stored']).read_bytes()
 assert hashlib.sha256(data).hexdigest()==e['stored_sha256'],logical
 raw=gzip.decompress(data) if e['encoding']=='gzip' else data
 assert len(raw)==e['bytes'] and hashlib.sha256(raw).hexdigest()==e['sha256'],logical
print('PASS',len(manifest),'archive hashes and all decoded payload hashes')
