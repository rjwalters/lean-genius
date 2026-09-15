"""Check complete saved stronger-host receipts with the independent 2670 API."""
import collections
import gzip
import hashlib
import importlib.util
import json
import time
import sys
from pathlib import Path
from inputs import load,OLD

P=Path(__file__).parent
part=int(sys.argv[1]);parts=4
assert 0<=part<parts
V=Path('/Users/rwalters/lean-genius-h7-host-pairrow-verifier-sol1-20260915')
for name,h in json.loads((V/'pins.json').read_text()).items():assert hashlib.sha256((V/name).read_bytes()).hexdigest()==h
spec=importlib.util.spec_from_file_location('reviewed_independent_verifier',V/'verifier.py')
v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
cover,cases,high=load()
result=json.loads((P/'results.json').read_text())
queue=json.loads((P/'queue.json').read_text())
assert len(queue)==result['queue']==18340
covered=json.loads((P/'covered-inputs.json').read_text())
full={(ci,pi) for ci,r in enumerate(high) for pi in range(len(r['pairings']))}
known={(r['case_index'],r['pairing_index']) for r in covered}
assert len(known)==68 and not known&set(map(tuple,queue)) and known|set(map(tuple,queue))==full

# Separate bitmask adapter from the producer's set-building graph().
def graph(ci,pi):
    si,sj,es=cases[ci];rep=cover['representatives'][si]
    g=[0]*49
    def add(u,w):g[u]|=1<<w;g[w]|=1<<u
    old=[0]*21
    for u,w in rep['F_edges']+es:old[u]|=1<<w;old[w]|=1<<u
    for s,hs in enumerate(rep['singleton_hosts'],7):
        for e in hs:old[s]|=1<<e;old[e]|=1<<s
    for u in range(21):
        for w in range(u):
            if old[u]>>w&1:add(u+42 if u<7 else u,w+42 if w<7 else w)
    for p in range(21,42):
        import itertools
        a,b=list(itertools.combinations(range(7),2))[p-21];add(p,a);add(p,b)
    for h,d in enumerate(high[ci]['pairings'][pi]):add(h,14+h);add(h,7+d)
    return [{w for w in range(49) if mask>>w&1} for mask in g]

pinfiles=[P/'results.json',P/'queue.json',P/'covered-inputs.json',P/'inputs.py']+[P/n for n in result['receipt_shards']]
pins={str(f):hashlib.sha256(f.read_bytes()).hexdigest() for f in pinfiles}
with (P/f'verification-launch-{part}.json').open('x') as f:
    json.dump({'aggregate_seconds':240,'part':part,'parts':parts,'max_nodes_per_endpoint':100000,'source_pins':pins,
               'verifier_pins_sha256':hashlib.sha256((V/'pins.json').read_bytes()).hexdigest()},f,indent=2)
start=time.monotonic();deadline=json.loads((P/'verification-plan.json').read_text())['deadline']
visited=selected=negative=leaves=pair_prunes=singleton_prunes=0;counts=collections.Counter()
for name in result['receipt_shards']:
    with gzip.open(P/name,'rt') as source:
        for line in source:
            r=json.loads(line);ci,pi=r['case_index'],r['pairing_index']
            assert [ci,pi]==queue[visited];visited+=1
            if (visited-1)%parts!=part:continue
            selected+=1
            cert=r['receipt'];counts[cert['status']]+=1
            if cert['status']=='UNKNOWN':continue
            assert cert['status']=='COMPLETE'
            remaining=deadline-time.monotonic()
            assert remaining>0,'Verification cap; producer remains frozen'
            checked=v.check(graph(ci,pi),cert,max_nodes=100000,seconds=remaining)
            assert checked['coverage_proved'] and checked['endpoint_status']=='PASS'
            negative+=not cert['solutions'];leaves+=len(cert['solutions'])
            pair_prunes+=checked['endpoint_counts'].get('pair_prunes',0)
            singleton_prunes+=checked['endpoint_counts'].get('singleton_prunes',0)
            if selected%100==0:
                (P/f'verification-progress-{part}.json').write_text(json.dumps({'status':'CHECKED_PREFIX_ONLY','visited':visited,
                    'counts':dict(counts),'negative_high_inputs':negative,'leaves':leaves,
                    'pair_prunes':pair_prunes,'singleton_prunes':singleton_prunes,'seconds':time.monotonic()-start})+'\n')
assert visited==result['visited'] and selected==len(range(part,visited,parts))

for name,h in pins.items():assert hashlib.sha256(Path(name).read_bytes()).hexdigest()==h
out={'status':'PASS_PART','part':part,'parts':parts,'selected':selected,'visited':visited,'unvisited':result['unvisited'],'counts':dict(counts),
     'negative_high_inputs':negative,'leaves':leaves,'pair_prunes':pair_prunes,'singleton_prunes':singleton_prunes,
     'seconds':time.monotonic()-start,'scope':'All COMPLETE stronger-host covers and endpoints checked; UNKNOWN/suffix unchanged; earlier68negative inputs inherited.'}
(P/f'verification-part-{part}.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
