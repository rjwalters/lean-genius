import gzip,hashlib,importlib.util,itertools,json,math,time
from pathlib import Path
P=Path('/Users/rwalters/lean-genius-h7-host-pairrow-sol2-20260915');O=Path(__file__).parent
F0=Path('/Users/rwalters/lean-genius-h7-f0-sol1-20260915')
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for manifest in ('pins.json','calibration-pins.json'):
    for n,h in read(P/manifest).items():assert sha(P/n)==h,n
l=read(P/'calibration-450k/launch.json')
assert l['source_pins_sha256']==sha(P/'pins.json') and l['driver_sha256']==sha(P/'calibrate_budget.py')
fixed=read(P/'cached/fixed-results.json');summary=read(P/'cached/fixture-summary.json')
reserve=10000*math.ceil(max(r['receipt']['nodes'] for r in fixed)/10000)
factor=math.ceil(max(r['nodes']/r['prior_nodes'] for r in summary if r['status']=='COMPLETE'))
assert (reserve,factor,l['max_nodes'],l['aggregate_seconds'])==(50000,4,450000,60)
inputs=[r for r in read(P/'cached/fixture-launch.json')['inputs'] if r['F_index']==0]
assert inputs==l['inputs'] and len(inputs)==8
prior=[]
for shard in read(F0/'host-results.json')['shards']:
    with gzip.open(F0/shard,'rt') as f:
        for line in f:
            r=json.loads(line)
            if r['receipt']['status']=='UNKNOWN':prior.append(r)
            if len(prior)==8:break
    if len(prior)==8:break
assert [(r['case_index'],r['pairing_index']) for r in prior]==[(r['case_index'],r['pairing_index']) for r in inputs]
assert all(r['receipt']['nodes']==100001 for r in prior)
high=read(F0/'high-results.json')['results'];source=Path(read(F0/'high-launch.json')['source_path'])
reps=read(source/'results.json')['representatives']
solutions={r['source_index']:r['solutions'] for r in read(source/'completion-results.json')['results'] if r['F_index']==0}
vp=Path('/Users/rwalters/lean-genius-h7-host-pairrow-verifier-sol1-20260915/verifier.py')
spec=importlib.util.spec_from_file_location('reviewed_verifier',vp);v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
checks=[];start=time.monotonic()
for j,fixture in enumerate(inputs):
    h=high[fixture['case_index']];rep=reps[h['source_index']];g=[set() for _ in range(49)]
    def add(a,b):g[a].add(b);g[b].add(a)
    ren=lambda u:u+42 if u<7 else u
    for a,b in rep['F_edges']+solutions[h['source_index']][h['singleton_index']]:add(ren(a),ren(b))
    for s,es in enumerate(rep['singleton_hosts'],7):
        for e in es:add(s,e+42)
    for p,(a,b) in enumerate(itertools.combinations(range(7),2),21):add(p,a);add(p,b)
    for hi,d in enumerate(h['pairings'][fixture['pairing_index']]):add(hi,14+hi);add(hi,7+d)
    assert [sorted(ns) for ns in g]==fixture['adjacency']
    saved=read(P/f'calibration-450k/receipt-{j:02d}.json');assert saved['input']==fixture
    r=saved['receipt'];assert r['status']=='COMPLETE' and not r['solutions'] and r['nodes']<=450000
    checked=v.check(g,r,max_nodes=450000,seconds=max(0,30-(time.monotonic()-start)))
    assert checked['coverage_proved'] and checked['endpoint_status']=='PASS';checks.append(checked)
out={'status':'PASS_EIGHT_CALIBRATION_INPUTS','inputs':8,'source_identity':'Exact first eight original F0 UNKNOWN keys; adjacency independently reconstructed',
     'reserve':reserve,'factor':factor,'budget':450000,'checks':checks,'seconds':time.monotonic()-start,
     'scope':'Eight fixed high inputs only, no whole F0 exclusion. Old capped records unchanged.'}
(O/'REVIEW.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k!='checks'})
