from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
m=json.loads((p/'manifest.json').read_text())
for name,digest in m.items():
 assert hashlib.sha256((p/name).read_bytes()).hexdigest()==digest,name
print('Verified',len(m),'archived payload files; no search replay')
