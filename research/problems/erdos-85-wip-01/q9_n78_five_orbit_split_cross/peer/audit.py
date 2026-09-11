from pathlib import Path
import itertools as it,json,hashlib,time
start=time.monotonic();src=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n78-five-orbit-split-cross');out=Path(__file__).resolve().parent;pins={}
def guard():
 if time.monotonic()-start>30:raise TimeoutError('Original independent30s audit cap exceeded')
for mf in ['pins.json','input-pins.json']:
 for n,h in json.loads((src/mf).read_text()).items():
  p=src/n;assert hashlib.sha256(p.read_bytes()).hexdigest()==h;pins[str(p)]=h
for r in json.loads((out/'premise-states.json').read_text()):assert r['status']=='resolved' and r['resolution'].startswith('PASS')
base=Path('/tmp/erdos85-sol1-q9-n78-four-orbit-order24-parameters');groups=json.loads((base/'groups.json').read_text());cubic=json.loads((base/'results.json').read_text())['records'];saved=json.loads((src/'results.json').read_text());assert saved['status']=='COMPLETE'
expected={(c['group'],tuple(c['H'])) for c in saved['contexts']};seen=set()
for gi,g in enumerate(groups):
 if not cubic[gi]['cubic_sets']:continue
 M=g['multiplication']
 for size in (1,2,3):
  for gens in it.combinations(range(1,24),size):
   guard();H={0};queue=[0]
   for x in queue:
    for y in gens:
     z=M[x][y]
     if z not in H:H.add(z);queue.append(z)
    if len(H)>8:break
   if len(H)==8:seen.add((gi,tuple(sorted(H))))
assert seen==expected and len(seen)==41
pairs=list(it.combinations(range(24),2));pairidx={p:i for i,p in enumerate(pairs)}
def pairmask(neighborhoods):
 mask=0
 for ns in neighborhoods:
  for a,b in it.combinations(sorted(ns),2):
   bit=1<<pairidx[(a,b)]
   if mask&bit:return None
   mask|=bit
 return mask
def mixedmask(left,right):
 mask=0
 for ls,rs in zip(left,right):
  for a in ls:
   for b in rs:
    bit=1<<(24*a+b)
    if mask&bit:return None
    mask|=bit
 return mask
results=[];positive_codegrees=0;positives=0;raw=0
for ci,ctx in enumerate(saved['contexts']):
 guard();M=groups[ctx['group']]['multiplication'];inv=groups[ctx['group']]['inverse'];H=set(ctx['H']);cosets=sorted({tuple(sorted(M[g][h] for h in H)) for g in range(24)},key=min);assert [list(c) for c in cosets]==ctx['cosets'];labels=[next(i for i,c in enumerate(cosets) if x in c) for x in range(24)];assert labels==ctx['labels']
 fixed=pairmask(cosets);ss={}
 for s in it.combinations(range(1,24),3):
  if {inv[x] for x in s}!=set(s) or {labels[x] for x in s}!={0,1,2}:continue
  ns=[[M[g][x] for x in s] for g in range(24)];pm=pairmask(ns)
  if pm is not None and not pm&fixed:ss[s]=(ns,pm|fixed)
 rec=saved['records'][ci];assert rec['status']=='COMPLETE' and set(ss)==set(map(tuple,rec['internal_sets']))
 found=set();cross=0
 for t in it.product(cosets[1],cosets[2]):
  guard();ti=tuple(inv[x] for x in t)
  if {labels[x] for x in ti}!={1,2}:continue
  cross+=1;raw+=len(ss)**2;tn=[[M[g][x] for x in t] for g in range(24)];tin=[[M[g][x] for x in ti] for g in range(24)];ucross=pairmask(tin);vcross=pairmask(tn)
  if ucross is None or vcross is None:continue
  us=[];vs=[]
  for s,(ns,pm) in ss.items():
   if not pm&ucross:
    mm=mixedmask(ns,tn)
    if mm is not None:us.append((s,mm))
   if not pm&vcross:
    mm=mixedmask(tin,ns)
    if mm is not None:vs.append((s,mm))
  for u,um in us:
   for v,vm in vs:
    if um&vm:continue
    found.add((u,v,t))
 assert cross==rec['cross_sets']
 assert found=={(tuple(x['U']),tuple(x['V']),tuple(x['T'])) for x in rec['survivors']}
 # Independent full positive adjacency checks.
 for u,v,t in found:
  guard();adj=[0]*54
  def edge(a,b):assert a!=b;adj[a]|=1<<b;adj[b]|=1<<a
  for f in range(3):edge(f,3+f)
  for g in range(24):
   edge(6+g,labels[g]);edge(30+g,3+labels[g])
   for s in u:edge(6+g,6+M[g][s])
   for s in v:edge(30+g,30+M[g][s])
   for x in t:edge(6+g,30+M[g][x])
  assert [n.bit_count() for n in adj]==[9]*6+[6]*48
  for a in range(54):
   for b in range(a):assert (adj[a]&adj[b]).bit_count()<=1;positive_codegrees+=1
 positives+=len(found);results.append({'context':ci,'internal_sets':len(ss),'cross_sets':cross,'survivors':len(found)})
result={'status':'COMPLETE','original_audit_cap_seconds':30,'seconds':time.monotonic()-start,'contexts':41,'raw_couplings':raw,'survivors':positives,'positive_codegrees':positive_codegrees,'records':results}
assert positives==22848 and result['seconds']<30
(out/'input-pins.json').write_text(json.dumps(pins,indent=2)+'\n');(out/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='records'}))
