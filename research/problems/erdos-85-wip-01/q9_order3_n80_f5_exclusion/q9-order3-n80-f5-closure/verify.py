from pathlib import Path
import json,hashlib
p=Path(__file__).resolve().parent;base=p.parent
def records(folder,file='receipts.jsonl'):return [json.loads(x) for x in (base/folder/file).read_text().splitlines()]
def checkpins(folder):
 d=base/folder;raw=json.loads((d/'pins.json').read_text());pins=raw.get('files',raw)
 for n,h in pins.items():assert hashlib.sha256((d/n).read_bytes()).hexdigest()==h,(folder,n)
 return hashlib.sha256((d/'pins.json').read_bytes()).hexdigest()
folders=['q9-order3-residual-quotient','q9-order3-attached-capacity','q9-order3-local-contingency','q9-order3-word-support-cover','q9-order3-permutation-symmetry','q9-order3-color-lp-cover','q9-order3-integer-color-cover','q9-order3-row-supported-color-cover','q9-order3-fractional-residual','q9-order3-double-budget','q9-order3-local-row-propagation']
checked={f:checkpins(f) for f in folders}
allcodes={r['representative_code'] for r in records('q9-order3-permutation-symmetry','orbits.jsonl')};assert len(allcodes)==1284
stages={}
stages['2201']={r['code'] for r in records('q9-order3-color-lp-cover') if r['status']=='EXACT_INFEASIBLE'}
stages['2204']={r['code'] for r in records('q9-order3-row-supported-color-cover') if r['status']=='COMPLETE_NEGATIVE'}
stages['2205']={r['code'] for r in records('q9-order3-fractional-residual','batch.jsonl') if r['status']=='EXACT_INFEASIBLE'}|{r['code'] for r in records('q9-order3-fractional-residual','repaired.jsonl') if r['status']=='EXACT_REPAIRED_INFEASIBLE'}
stages['2209']={r['code'] for r in json.loads((base/'q9-order3-double-budget/results.json').read_text())['records'] if r['status']=='EXACT_INFEASIBLE'}
last=records('q9-order3-local-row-propagation');assert last[-1]['status']=='FIXPOINT' and last[-1]['remaining']==0
stages['2214']={24538199};seen=set()
for name,values in stages.items():assert not(seen&values),name;seen|=values
assert seen==allcodes;assert [len(x) for x in stages.values()]==[708,516,58,1,1]
reviews=json.loads((p/'reviews.json').read_text());pending=[r['id'] for r in reviews if r['status']!='resolved' or not (r.get('resolution') or '').startswith('PASS')]
out={'artifact_hashes_verified':checked,'representative_count':len(allcodes),'disjoint_stage_counts':{k:len(v) for k,v in stages.items()},'exact_cover':True,'pending_reviews':pending,'status':'VERIFIED_ACCEPTED_FINITE_CHAIN' if not pending else 'EXACT_COVER_PENDING_PEER_REVIEW'}
(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
