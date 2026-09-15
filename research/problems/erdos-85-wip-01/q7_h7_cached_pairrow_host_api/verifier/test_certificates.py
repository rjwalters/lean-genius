"""Check saved integrated receipts plus positive and corrupted controls."""
import copy,gzip,hashlib,itertools,json,time
from pathlib import Path
import verifier
P=Path(__file__).parent
I=Path('/Users/rwalters/lean-genius-h7-host-pairrow-sol2-20260915')
S=Path('/Users/rwalters/lean-genius-h7-f3-sol1-20260915')
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
paths=[I/v/n for v in ('baseline','cached') for n in ('fixture-results.json','fixed-results.json','fixture-launch.json')]
paths += [S/'residual-pins.json',S/'host-pins.json']
pins={str(p):sha(p) for p in paths}
with (P/'test-launch-v2.json').open('x') as f:json.dump({'seconds_cap':90,'inputs':pins,'correction':'Join adjacency from fixture-launch inputs; initial test stopped at missing metadata key.'},f,indent=2)
start=time.monotonic();end=start+90;results=[];rejected=0
for variant in ('baseline','cached'):
    def key(r):return r['F_index'],r['case_index'],r['pairing_index']
    inputs={key(r):r for r in read(I/variant/'fixture-launch.json')['inputs']}
    for r in read(I/variant/'fixture-results.json'):
        checked=verifier.check(inputs[key(r['fixture'])]['adjacency'],r['receipt'],verify_partial=True,seconds=end-time.monotonic())
        assert checked['endpoint_status']=='PASS'
        assert checked['coverage_proved']==(r['receipt']['status']=='COMPLETE')
        results.append(dict(variant=variant,kind='whole-input-receipt',**checked))
    for r in read(I/variant/'fixed-results.json'):
        checked=verifier.check(r['input']['adjacency'],r['receipt'],fixed=r['input']['fixed'],seconds=end-time.monotonic())
        assert checked['coverage_proved'] and checked['endpoint_status']=='PASS'
        results.append(dict(variant=variant,kind='fixed-control',**checked))
    r=read(I/variant/'fixed-results.json')[0]
    bad=copy.deepcopy(r['receipt']);bad['prunes']=[]
    try:verifier.check(r['input']['adjacency'],bad,fixed=r['input']['fixed'],seconds=1)
    except (AssertionError,TimeoutError):rejected+=1
    else:raise AssertionError('Missing certificate endpoint was accepted')

# Choose a saved ARC-negative leaf, which has nonempty individual row domains.
key=None
for name in read(S/'residual/results.json')['receipt_shards']:
    with gzip.open(S/'residual'/name,'rt') as f:
        for line in f:
            r=json.loads(line)
            for li,x in enumerate(r['receipts']):
                if x['status']=='INFEASIBLE_ARC':key=(r['case_index'],r['pairing_index'],li);break
            if key:break
    if key:break
assert key
ci,pi,li=key;chosen=None
with gzip.open(S/'residual/source-leaves.jsonl.gz','rt') as f:
    for line in f:
        r=json.loads(line)
        if (r['case_index'],r['pairing_index'])==(ci,pi):chosen=[m<<21 for m in r['hosts'][li]];break
assert chosen is not None
launch=read(S/'high-launch.json');source=Path(launch['source_path'])
h=read(S/'high-results.json')['results'][ci];rep=read(source/'results.json')['representatives'][h['source_index']]
es=next(r['solutions'][h['singleton_index']] for r in read(source/'completion-results.json')['results'] if r['source_index']==h['source_index'])
g=[set() for _ in range(49)]
def add(u,v):g[u].add(v);g[v].add(u)
ren=lambda u:42+u if u<7 else u
for u,v in rep['F_edges']+es:add(ren(u),ren(v))
for s,hs in enumerate(rep['singleton_hosts'],7):
    for e in hs:add(s,e+42)
for p,(u,v) in enumerate(itertools.combinations(range(7),2),21):add(p,u);add(p,v)
for hi,d in enumerate(h['pairings'][pi]):add(hi,14+hi);add(hi,7+d)
positive={'status':'COMPLETE','empty_vertices':list(range(42,49)),'order':list(range(7)),
          'solutions':[chosen],'prunes':[]}
checked=verifier.check(g,positive,fixed=chosen,seconds=end-time.monotonic())
assert checked['endpoint_counts']['positive_leaves']==1
results.append(dict(variant='synthetic-valid',kind='positive-fixed-leaf',**checked))
for bad in [dict(positive,solutions=[],prunes=[{'depth':7,'pair_vertex':21,'future_pairs':0,'chosen':chosen}]),
            dict(positive,solutions=[],prunes=[{'depth':7,'singleton':7,'chosen':chosen}]),
            dict(positive,solutions=[],prunes=[{'depth':7,'pair_vertex':21,'future_pairs':1,'chosen':chosen}])]:
    try:verifier.check(g,bad,fixed=chosen,seconds=1)
    except (AssertionError,TimeoutError):rejected+=1
    else:raise AssertionError('False negative certificate accepted')
unknown=dict(positive,status='UNKNOWN',solutions=[])
assert not verifier.check(g,unknown,fixed=chosen,seconds=1)['coverage_proved']
for p,h in pins.items():assert sha(Path(p))==h
summary={'status':'PASS_SAVED_RECEIPTS_AND_CONTROLS','receipts':len(results),
         'whole_coverage_proved':sum(r['coverage_proved'] for r in results),
         'negative_checks':sum(sum(v for k,v in r['endpoint_counts'].items() if k.endswith('prunes')) for r in results),
         'positive_leaf_controls':1,'corruptions_rejected':rejected,'seconds':time.monotonic()-start,
         'results':results,'scope':'Verifier controls and saved calibration receipts only; no new host producer run or root exclusion.'}
(P/'test-results.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='results'}))
