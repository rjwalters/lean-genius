from pathlib import Path
import json,hashlib,sqlite3
s=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3');p=Path(__file__).resolve().parent
packages=['q9-order3-permutation-symmetry','q9-order3-color-lp-cover','q9-order3-row-supported-color-cover','q9-order3-fractional-residual','q9-order3-double-budget','q9-order3-local-row-propagation']
for package in packages:
 src=s/package
 for f,h in json.loads((src/'pins.json').read_text()).items():assert hashlib.sha256((src/f).read_bytes()).hexdigest()==h,(package,f)
def receipts(name):return list(map(json.loads,(s/name/'receipts.jsonl').read_text().splitlines()))
lp=receipts('q9-order3-color-lp-cover');universe={r['code'] for r in lp};assert len(lp)==len(universe)==1284
parts={2201:{r['code'] for r in lp if r['status']=='EXACT_INFEASIBLE'},2204:{r['code'] for r in receipts('q9-order3-row-supported-color-cover') if r['status']=='COMPLETE_NEGATIVE'}}
f=s/'q9-order3-fractional-residual';rr=list(map(json.loads,(f/'batch.jsonl').read_text().splitlines()))+list(map(json.loads,(f/'repaired.jsonl').read_text().splitlines()))
parts[2205]={r['code'] for r in rr if r['status'] in ('EXACT_INFEASIBLE','EXACT_REPAIRED_INFEASIBLE')}
parts[2209]={r['code'] for r in json.loads((s/'q9-order3-double-budget/results.json').read_text())['records'] if r['status']=='EXACT_INFEASIBLE'};parts[2214]={24538199}
seen=set()
for k,part in parts.items():assert not seen&part;seen|=part
assert seen==universe and [len(x) for x in parts.values()]==[708,516,58,1,1]
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
for review in [2176,2179,2184,2190,2191,2194,2199,2200,2201,2203,2204,2205,2209]:
 status,res=c.execute('select status,resolution from review_requests where id=?',(review,)).fetchone();assert status=='resolved' and res.startswith('PASS'),review
out={'status':'PASS_EXACT_PARTITION','total_representatives':1284,'disjoint_exclusions_by_review':{str(k):len(v) for k,v in parts.items()},'uncovered':0,'all_predecessor_reviews_accepted':True,'scope':'N80 order-three automorphism fixing exactly five vertices'}
(p/'coverage.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
