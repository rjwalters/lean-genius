from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
payload=json.loads((root/'payload-pins.json').read_text())
for name,h in payload.items():assert hashlib.sha256((root/name).read_bytes()).hexdigest()==h,name
closure=json.loads((root/'q9-order3-n80-f5-closure/results.json').read_text())
for folder,h in closure['artifact_hashes_verified'].items():
 p=root/folder;assert hashlib.sha256((p/'pins.json').read_bytes()).hexdigest()==h
 pins=json.loads((p/'pins.json').read_text());pins=pins.get('files',pins)
 for name,digest in pins.items():assert hashlib.sha256((p/name).read_bytes()).hexdigest()==digest,(folder,name)
reviews=json.loads((root/'q9-order3-n80-f5-closure/reviews.json').read_text())
assert all(r['status']=='resolved' and r['resolution'].startswith('PASS') for r in reviews)
def read(folder,name='receipts.jsonl'):return [json.loads(x) for x in (root/folder/name).read_text().splitlines()]
allcodes={r['representative_code'] for r in read('q9-order3-permutation-symmetry','orbits.jsonl')}
stages=[{r['code'] for r in read('q9-order3-color-lp-cover') if r['status']=='EXACT_INFEASIBLE'}, {r['code'] for r in read('q9-order3-row-supported-color-cover') if r['status']=='COMPLETE_NEGATIVE'}, {r['code'] for r in read('q9-order3-fractional-residual','batch.jsonl') if r['status']=='EXACT_INFEASIBLE'}|{r['code'] for r in read('q9-order3-fractional-residual','repaired.jsonl') if r['status']=='EXACT_REPAIRED_INFEASIBLE'}, {r['code'] for r in json.loads((root/'q9-order3-double-budget/results.json').read_text())['records'] if r['status']=='EXACT_INFEASIBLE'}, {24538199}]
last=read('q9-order3-local-row-propagation')[-1];assert last['status']=='FIXPOINT' and last['remaining']==0
seen=set()
for stage in stages:assert not(seen&stage);seen|=stage
assert seen==allcodes and len(allcodes)==1284 and [len(s) for s in stages]==[708,516,58,1,1]
print(json.dumps({'status':'PASS','payload_hashes':len(payload),'accepted_reviews':len(reviews),'disjoint_case_counts':[len(s) for s in stages],'total':len(allcodes)}))
