"""Read-only integrity and finite coverage verification; no solver calls."""
from pathlib import Path
import hashlib,json,runpy
p=Path(__file__).resolve().parent
def read(name):return json.loads((p/name).read_text())
pins=read('payload-pins.json')
for name,digest in pins.items():
 path=p/name
 assert path.resolve().is_relative_to(p),name
 assert hashlib.sha256(path.read_bytes()).hexdigest()==digest,name
for artifact in read('provenance.json'):
 directory=p/artifact['archive_directory']
 for name,digest in json.loads((directory/artifact['pin_file']).read_text()).items():
  assert hashlib.sha256((directory/name).read_bytes()).hexdigest()==digest,name
reviews=read('accepted-reviews.json')
assert {r['id'] for r in reviews}=={2220,2223,2225,2233}
assert all(r['status']=='resolved' and r['resolution'].startswith('PASS') for r in reviews)
result=read('q9-involution-four-orbit-cover/results.json')
assert result['status']=='COMPLETE' and result['inputs']==1024
assert (result['retained'],result['symmetry_classes'],result['allocation_count'])==(243,24,4507)
runpy.run_path(str(p/'q9-involution-four-orbit-cover/verify.py'),run_name='__main__')
print(f'PASS: {len(pins)} payload hashes, eight original pin manifests, four accepted reviews, and exact quotient coverage.')
