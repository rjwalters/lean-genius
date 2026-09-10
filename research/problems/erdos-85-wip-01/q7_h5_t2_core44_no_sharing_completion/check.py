from pathlib import Path
import json,itertools,time,hashlib
p=Path(__file__).parent;cp=p/'canonical-source.json';ep=p/'four-pattern-source.json'
cd=json.loads(cp.read_text());ed=json.loads(ep.read_text());names=cd['names']+['E'+str(i) for i in range(12)];idx={n:i for i,n in enumerate(names)};results=[]
def vertices(bits):
 while bits:
  b=bits&-bits;yield b.bit_length()-1;bits^=b
for c in cd['canonical_configurations']:
 if c['af']!=3 or c['bf']!=2:continue
 for e in ed['results']:
  g=[sum(1<<v for v in ns) for ns in c['adjacency']]+[0]*12
  trans={v:v for v in range(11)};trans.update({11+i:37+i for i in range(12)});trans.update({23:idx['a0'],24:idx['b0'],25:idx['b2'],26:idx['b4']})
  for u,ns in enumerate(e['skeleton']):
   for v in ns:g[trans[u]]|=1<<trans[v]
  initial=g.copy();trace=[];status='FIXED_POINT';failure=None
  def clean():return all((g[u]&g[v]).bit_count()<=1 for u,v in itertools.combinations(range(49),2))
  if not clean():status='EXCLUDED';failure={'reason':'initial C4'}
  while status=='FIXED_POINT':
   deg=[x.bit_count() for x in g];targets=[8]*5+[7]*44
   if any(deg[u]>targets[u] for u in range(49)):status='EXCLUDED';failure={'reason':'degree excess'};break
   cand=[[] for _ in range(49)]
   for u,v in itertools.combinations(range(5,49),2):
    if deg[u]>=7 or deg[v]>=7 or g[u]>>v&1:continue
    if any(g[w]&g[v] for w in vertices(g[u])):continue
    cand[u].append(v);cand[v].append(u)
   forced=None
   for u in range(5,49):
    need=7-deg[u]
    if len(cand[u])<need:status='EXCLUDED';failure=dict(reason='degree shortage',vertex=names[u],need=need,candidates=[names[v] for v in cand[u]]);break
    if need and len(cand[u])==need:forced=(u,cand[u][0],'degree');break
    for colour in range(5):
     if g[u]&g[colour]:continue
     options=[v for v in cand[u] if g[v]>>colour&1]
     if not options:status='EXCLUDED';failure=dict(reason='missing high colour',vertex=names[u],colour=colour);break
     if len(options)==1:forced=(u,options[0],'colour'+str(colour));break
    if forced or status=='EXCLUDED':break
   if status=='EXCLUDED' or forced is None:break
   u,v,why=forced;trace.append(dict(edge=[u,v],reason=why));g[u]|=1<<v;g[v]|=1<<u
   assert clean()
  results.append(dict(af=3,bf=2,f3_d3_edge=c['f3_d3_edge'],omitted=e['omitted'],status=status,failure=failure,forced_edges=len(trace),trace=trace,initial=initial,adjacency=g))
  print({k:v for k,v in results[-1].items() if k not in ['trace','initial','adjacency']},flush=True)
(p/'results.json').write_text(json.dumps(dict(source_pins={str(cp):hashlib.sha256(cp.read_bytes()).hexdigest(),str(ep):hashlib.sha256(ep.read_bytes()).hexdigest()},names=names,results=results,scope='Eight full49vertex labelled starting graphs from independent own-colour naming and reviewed distinguished-empty cover. Deterministic necessary degree/colour forcing only; no branching/capped retry.'),indent=2)+'\n')
