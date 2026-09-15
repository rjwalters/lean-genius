import hashlib,json,sqlite3
from pathlib import Path
D=Path(__file__).parent;P=Path('/Users/rwalters/lean-genius-h7-a6-f14-incidence-cover-sol2-20260915');A=Path('/Users/rwalters/lean-genius-h7-a6-f14-incidence-native-sol2-20260915')
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for base in [P,A]:
 for n,h in read(base/'pins.json').items():assert sha(base/n)==h
l=read(P/'launch.json');r=read(P/'results.json');assert l['driver_sha256']==sha(P/'run.py') and l['api_pins_sha256']==sha(A/'pins.json')
assert r['seconds']<l['aggregate_seconds']==300 and l['nodes_per_case']==10000
assert r['artifact_bytes']<l['artifact_byte_cap']==200000000 and l['shard_byte_cap']==50000000
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
for rid,res in l['reviews'].items():
 st,current=c.execute('select status,resolution from review_requests where id=?',(int(rid),)).fetchone();assert st=='resolved' and current==res
for n,m in read(P/'receipt-locations.json')['files'].items():
 path=Path(m['path']);assert sha(path)==m['sha256']==sha(P/n) and path.stat().st_size==m['bytes']==(P/n).stat().st_size
for n,h in read(D/'launch.json')['input_hashes'].items():assert sha(Path(n))==h
out={'status':'PASS_FINAL_PROVENANCE_AND_DURABLE_RECEIPT','author_manifest_sha256':sha(P/'pins.json'),'api_manifest_sha256':sha(A/'pins.json'),'locator':read(P/'receipt-locations.json'),'scope':'Final producer/API pins, exact live launch reviews, original audit inputs and durable receipt hash/size. Certificate verification is separate.'}
(D/'PROVENANCE_REVIEW.json').write_text(json.dumps(out,indent=2)+'\n');print(out['status'])
