from pathlib import Path
import json,itertools as it,time,hashlib
out=Path(__file__).resolve().parent
src=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n78-five-orbit-single-cross')
base=Path('/tmp/erdos85-sol1-q9-n78-four-orbit-order24-parameters')
pins={}
for name in ('pins.json','input-pins.json'):
 for n,h in json.loads((src/name).read_text()).items():
  p=src/n;assert hashlib.sha256(p.read_bytes()).hexdigest()==h;pins[str(p)]=h
for r in json.loads((out/'premise-states.json').read_text()):assert r['status']=='resolved' and r['resolution'].startswith('PASS')
groups=json.loads((base/'groups.json').read_text());params=json.loads((base/'results.json').read_text())['records'];saved=json.loads((src/'results.json').read_text());assert saved['status']=='COMPLETE'
expected={(gi,ai,a) for gi,p in enumerate(params) for ai in range(len(p['actions'])) for a in range(1,5)}
records={(r['group'],r['action'],r['a']):r for r in saved['records']};assert len(records)==len(saved['records'])==844 and set(records)==expected
start=time.monotonic();cache={};report=[];codegrees=0

def guard():
 if time.monotonic()-start>30:raise TimeoutError('Original independent audit cap 30 seconds')
def signature(xs,ys,same=False):
 bits=0
 for x in xs:
  for y in ys:
   if same and x==y:continue
   bit=1<<D[x][y]
   if bits&bit:return None
   bits|=bit
 return bits
for (gi,ai,a),rec in records.items():
 guard();g=groups[gi];M=g['multiplication'];inv=g['inverse'];D=[[M[x][inv[y]] for y in range(24)] for x in range(24)]
 act=params[gi]['actions'][ai];labels=act['labels'];H=set(act['H']);assert H=={x for x in range(24) if labels[x]==0}
 allowed=set(range(6))-{act['partner']};fixed=sum(1<<x for x in H);fixed_nonzero=fixed-1
 if (gi,a) not in cache:
  candidates=[]
  for xs in it.combinations(range(1,24),a):
   if any(inv[x] not in xs for x in xs):continue
   sig=signature(xs,xs,True)
   if sig is not None:candidates.append((xs,sig))
  cache[gi,a]=candidates
 ss={};bylabels={}
 for xs,sig in cache[gi,a]:
  labs=frozenset(labels[x] for x in xs)
  if len(labs)!=a or not labs<=allowed or sig&fixed_nonzero:continue
  ss[xs]=sig;bylabels.setdefault(labs,[]).append(xs)
 assert rec['status']=='COMPLETE' and set(ss)==set(map(tuple,rec['internal_sets']))
 found=set()
 for u,us in ss.items():
  fibers=[[x for x in range(24) if labels[x]==f] for f in sorted(allowed-{labels[x] for x in u})]
  for t in it.product(*fibers):
   ti=tuple(inv[x] for x in t);labs=frozenset(labels[x] for x in ti)
   if len(labs)!=len(ti) or not labs<=allowed:continue
   vs=bylabels.get(frozenset(allowed-labs),[])
   if not vs:continue
   ts=signature(t,t,True)
   if ts is None or ts&(us|fixed_nonzero):continue
   tis=signature(ti,ti,True)
   if tis is None or tis&fixed_nonzero:continue
   mixed=signature(u,ti)
   if mixed is None or mixed&fixed:continue
   for v in vs:
    if ss[v]&tis:continue
    mv=signature(t,v)
    if mv is None or mv&(mixed|fixed):continue
    found.add((u,v,t))
 assert found=={(tuple(x['U']),tuple(x['V']),tuple(x['T'])) for x in rec['survivors']}
 for u,v,t in found:
  adj=[0]*54
  def edge(x,y):
   assert x!=y
   adj[x]|=1<<y;adj[y]|=1<<x
  for f,p in enumerate(act['matching']):edge(f,p)
  for x in range(24):
   edge(6+x,labels[x]);edge(30+x,labels[x])
   for y in u:edge(6+x,6+M[x][y])
   for y in v:edge(30+x,30+M[x][y])
   for y in t:edge(6+x,30+M[x][y])
  assert [n.bit_count() for n in adj]==[9]*6+[6]*48
  for x in range(54):
   for y in range(x):assert (adj[x]&adj[y]).bit_count()<=1
  codegrees+=1431
 report.append({'group':gi,'action':ai,'a':a,'survivors':len(found)})
result={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'roots':len(report),'survivors':sum(r['survivors'] for r in report),'positive_roots':sum(r['survivors']>0 for r in report),'by_degree':{a:sum(r['survivors'] for r in report if r['a']==a) for a in range(1,5)},'positive_codegrees':codegrees,'records':report}
assert result['seconds']<30 and result['survivors']==12928 and codegrees==18499968
(out/'verification.json').write_text(json.dumps(result,indent=2)+'\n');(out/'input-pins.json').write_text(json.dumps(pins,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='records'}))
