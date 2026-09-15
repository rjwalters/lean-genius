import json,hashlib,gzip,itertools,time,sqlite3
from pathlib import Path
P=Path('/Users/rwalters/lean-genius-h7-f8-sol2-20260915');OUT=Path(__file__).parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
start=time.monotonic()
pins=json.loads((P/'host-pins.json').read_text())
for n,h in pins.items():assert sha(P/n)==h
launch=json.loads((P/'high-launch.json').read_text());S=Path(launch['source_path'])
for n,h in launch['source_pins'].items():assert sha(S/n)==h
cover=json.loads((S/'results.json').read_text());done=json.loads((S/'completion-results.json').read_text())
cases=[(r['source_index'],j,es) for r in done['results'] if r['F_index']==8 for j,es in enumerate(r['solutions'])]
high=json.loads((P/'high-results.json').read_text())['results']
assert len(cases)==len(high)==5818
for ci,((si,sj,es),h) in enumerate(zip(cases,high)):
 assert (h['case_index'],h['source_index'],h['singleton_index'])==(ci,si,sj)
 assert h['status']=='COMPLETE'
 rep=cover['representatives'][si]
 assert rep['F_index']==8
 # independent bit adjacency corresponds to both audited source adapters
 g=[0]*49
 def add(u,v):g[u]|=1<<v;g[v]|=1<<u
 ren=lambda v:v+42 if v<7 else v
 for u,v in rep['F_edges']+es:add(ren(u),ren(v))
 for s,hosts in enumerate(rep['singleton_hosts'],7):
  for e in hosts:add(s,e+42)
 for p,(u,v) in enumerate(itertools.combinations(range(7),2),21):add(p,u);add(p,v)
 assert all(g[v].bit_count()<=7 for v in range(7,49))
expected=((ci,pi) for ci,h in enumerate(high) for pi in range(len(h['pairings'])))
r=json.loads((P/'hosts/results.json').read_text());v=json.loads((P/'host-verification.json').read_text())
visited=leaves=prunes=negative=nodes=0
for name in r['receipt_shards']:
 assert (P/'hosts'/name).stat().st_size<50000000
 for line in gzip.open(P/'hosts'/name,'rt'):
  assert time.monotonic()-start<90
  d=json.loads(line);ci,pi=next(expected)
  assert (ci,pi)==(d['case_index'],d['pairing_index'])
  h=high[ci];assert (d['source_index'],d['singleton_index'])==(h['source_index'],h['singleton_index'])
  c=d['receipt'];assert c['status']=='COMPLETE'
  visited+=1;leaves+=len(c['solutions']);prunes+=len(c['prunes']);negative+=not c['solutions'];nodes+=c['nodes']
assert next(expected,None) is None
assert (visited,leaves,prunes,negative)==(125268,368456,15261019,30934)
assert (v['visited'],v['leaves'],v['prunes'],v['negative'])==(visited,leaves,prunes,negative)
assert r['nodes']==nodes and r['unvisited']==v['unvisited']==0
assert r['counts']==v['counts']=={'COMPLETE':125268}
vl=json.loads((P/'host-verification-launch.json').read_text())
for n,h in vl['pins'].items():assert sha(Path(n))==h
hl=json.loads((P/'hosts/launch.json').read_text());api=Path(hl['api_path'])
for n,h in hl['api_pins'].items():assert sha(api/n)==h
assert hl['runner_sha256']==sha(P/'hosts.py')
assert r['seconds']<hl['aggregate_seconds']==300
assert sum((P/'hosts'/n).stat().st_size for n in r['receipt_shards'])==r['artifact_bytes']<hl['artifact_byte_cap']==350000000
assert v['seconds']<vl['aggregate_seconds']==300
mapping=json.loads((P/'f8-root-mapping.json').read_text())
frozen=Path('/Users/rwalters/lean-genius-cayley-sol1-20260913/h7-frontier-map-20260915/results.json')
assert sha(frozen)==mapping['source_sha256']
assert sum(1<<i for i,e in enumerate(itertools.combinations(range(7),2)) if list(e) in mapping['target_edges'])==1343559
assert mapping['matches'][0]['root']['id']=='cube_F7_t8'
assert mapping['matches'][0]['parent_to_F8']==list(range(7))
db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
for rid in [2116,2123,2124,2676]:
 st,res=db.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert st=='resolved' and res.startswith('PASS')
result=dict(status='PASS',visited=visited,leaves=leaves,prunes=prunes,negative=negative,pins=len(pins),seconds=time.monotonic()-start,scope='Independent full source/receipt accounting and checker execution audit; did not repeat 15m endpoints. Necessary graph host cover only, not residual or kernel exclusion.')
(OUT/'REVIEW.json').write_text(json.dumps(result,indent=2)+'\n')
(OUT/'pins.json').write_text(json.dumps({n:sha(OUT/n) for n in ['audit.py','REVIEW.json']},indent=2)+'\n')
print(json.dumps(result))
