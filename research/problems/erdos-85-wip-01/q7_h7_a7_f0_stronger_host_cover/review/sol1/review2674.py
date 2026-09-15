import hashlib,itertools,json,sqlite3
from pathlib import Path
P=Path('/Users/rwalters/lean-genius-h7-f0-pairrow-sol2-20260915');O=Path(__file__).parent
read=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=read(P/'host-pins.json')
for n,h in pins.items():assert sha(P/n)==h
join=read(O/'join-result.json');ad=read(O/'adapters-result.json')
assert join['status']=='PASS_EXACT_REUSE_AND_QUEUE_JOIN' and ad['inputs']==18408
for n,h in ad['pins'].items():assert sha(Path(n))==h
res=read(P/'results.json');queue=read(P/'queue.json');parts=[read(P/f'verification-part-{i}.json') for i in range(4)]
for i,r in enumerate(parts):
    assert r['status']=='PASS_PART' and r['part']==i and r['parts']==4
    assert r['visited']==18340 and r['selected']==len(queue[i::4])
    assert r['counts']=={'COMPLETE':r['selected']} and r['unvisited']==0 and r['seconds']<240
    launch=read(P/f'verification-launch-{i}.json')
    assert launch['part']==i and launch['parts']==4 and launch['aggregate_seconds']==240
    for n,h in launch['source_pins'].items():assert sha(Path(n))==h
    V=Path('/Users/rwalters/lean-genius-h7-host-pairrow-verifier-sol1-20260915')
    assert sha(V/'pins.json')==launch['verifier_pins_sha256']
    for n,h in read(V/'pins.json').items():assert sha(V/n)==h
for field,key in [('negative_high_inputs','new_negative'),('leaves','leaves'),('pair_prunes','pair_prunes'),('singleton_prunes','singleton_prunes')]:
    assert sum(r[field] for r in parts)==join[key]
root=read(P/'root-mapping.json')
assert root['parent_to_F0']==list(range(7))
assert sum(1<<i for i,e in enumerate(itertools.combinations(range(7),2)) if list(e) in root['edges'])==139591==root['root']['mask']
assert root['root']['id']=='cube_F7_t0'
H=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01/h7-frontier-map-20260915')
historical=next(p for p in H.rglob('*.json') if sha(p)==root['source_sha256'])
def objects(x):
    if isinstance(x,dict):
        yield x
        for v in x.values():yield from objects(v)
    elif isinstance(x,list):
        for v in x:yield from objects(v)
assert root['root'] in list(objects(read(historical)))
db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
for rid in (2116,2654,2656,2669,2670,2672):
    r=db.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert r[0]=='resolved' and r[1].startswith('PASS')
out={'status':'PASS_REVIEW2674','payloads':len(pins),'high_inputs':18408,'reused_negative':68,'new_negative':17632,'residual_leaves':3012,'pair_prunes':7488293,'singleton_prunes':1277058,'root':'cube_F7_t0','mask':139591,'checks':'Independent exact original reuse/queue/receipt accounting, every graph adapter, pins and disjoint verifier partition reconciliation; audited reviewed checker execution. No independent repetition of all endpoints in this review.','scope':'Necessary host cover only. Source2116 completeness rests on code audit; residual/F0/global/Lean remain open.'}
(O/'REVIEW2674.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
