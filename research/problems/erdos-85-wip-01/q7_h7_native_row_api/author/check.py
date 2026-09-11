import pathlib,importlib.util,json,gzip,time,hashlib,copy
from native import check,lib
P=pathlib.Path(__file__).parent;reference=P.parent/'h7-fast-row-api/filter.py'
spec=importlib.util.spec_from_file_location('reference',reference);ref=importlib.util.module_from_spec(spec);spec.loader.exec_module(ref)
fixtures=[r['adjacency'] for r in json.loads((P.parent/'h7-row-compatibility/domains.json').read_text())['results']]
with gzip.open(P.parent/'h7-twin4-arc/results.json.gz','rt') as f:data=json.load(f)
for status in ['INFEASIBLE_LOCAL','INFEASIBLE_ARC']:
 candidates=[r['adjacency'] for r in data['results'] if r['status']==status]
 fixtures.extend(candidates[i] for i in [0,len(candidates)//2,len(candidates)-1])
del data
(P/'fixtures.json').write_text(json.dumps(fixtures)+'\n')
results=[]
for i,g in enumerate(fixtures):
 for cap in [0,1,1000,100000]:
  t=time.monotonic();a=ref.check(g,max_nodes=cap);py=time.monotonic()-t
  t=time.monotonic();b=check(g,max_nodes=cap);native=time.monotonic()-t
  assert a==b,(i,cap,{k:v for k,v in a.items() if k not in ['initial','events']},{k:v for k,v in b.items() if k not in ['initial','events']})
  results.append(dict(fixture=i,budget=cap,status=a['status'],nodes=a['nodes'],identical_entire_result=True,python_seconds=py,native_seconds=native))
 assert check(g,deadline=time.monotonic()-1)==ref.check(g,deadline=time.monotonic()-1)
# Invalid graphs must not be used for pruning.
bad=copy.deepcopy(fixtures[0]);bad[0].append(0)
try:check(bad)
except ValueError:pass
else:raise AssertionError('accepted selfloop')
# The C boundary must use the same absolute clock as the Python deadline.
clock_delta=abs(lib.native_now()-time.monotonic());assert clock_delta<0.01
out=dict(status='PASS',fixtures=len(fixtures),comparisons=results,expired_deadline_equalities=len(fixtures),clock_delta=clock_delta,reference_sha256=hashlib.sha256(reference.read_bytes()).hexdigest(),scope='Equivalence tests only on already-terminal fixed graphs; no cappedresearchcase retry or new profile search.')
(P/'results.json').write_text(json.dumps(out,indent=2)+'\n')
full=[r for r in results if r['budget']==100000]
print('PASS',len(results),'fullobject comparisons;',len(fixtures),'expireddeadlines; fullbudget seconds',sum(r['python_seconds'] for r in full),sum(r['native_seconds'] for r in full))
