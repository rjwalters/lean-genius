from pathlib import Path
import json,itertools as it,time,hashlib
b=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3');o=Path(__file__).parent
def read(f):return json.loads(f.read_text())
names=['residual-ten-D5-five-311-center-domains','residual-ten-D5-five-311-center-cover'];nh=0
for name in names:
 p=b/name
 for fn in ['pins.json','input-pins.json']:
  for k,v in read(p/fn).items():
   q=Path(k);q=q if q.is_absolute() else p/q
   assert hashlib.sha256(q.read_bytes()).hexdigest()==v;nh+=1
domain=read(b/names[0]/'results.json');cover=read(b/names[1]/'results.json');assert domain['status']==cover['status']=='COMPLETE'
models={r['root']:r for r in read(b/'residual-ten-D5-five-311-low-orbit-capacity/models.json')['records']};results=read(b/'residual-ten-D5-five-311-low-orbit-capacity/results.json')['records'];prop={r['root']:r for r in read(b/'residual-ten-D5-five-311-low-propagation/results.json')['records']};edges={r['root']:r for r in read(b/'residual-ten-D5-five-311-low-edge-capacity/results.json')['records']};joint={r['root']:r for r in read(b/'residual-ten-D5-five-311-nonempty-joint/results.json')['records']};graphs={r['root']:r for r in read(b/'residual-ten-D5-five-311-high-matchings/results.json')['records']};pack=read(b/'residual-ten-D5-five-311-packing/results.json')['records'];dom=read(b/'residual-ten-D5-supports/results.json')['records']
lookup={r['root']:r for r in domain['records']};assert len(lookup)==len(domain['records'])==41 and lookup.keys()=={r['root'] for r in results if r['status']=='EXACT_RATIONAL_WITNESS'}
def matchings(rem):
 if not rem:yield ();return
 v=rem[0]
 yield from matchings(rem[1:])
 for j,w in enumerate(rem[1:],1):
  for rest in matchings(rem[1:j]+rem[j+1:]):yield ((v,w),)+rest
patterns=list(matchings(tuple(range(6))));assert len(patterns)==76
start=time.monotonic();status='INCOMPLETE';highcount=lowcount=0
def guard():
 if time.monotonic()-start>30:raise TimeoutError
try:
 for key,rec in lookup.items():
  guard();m=models[key];src=m['source_root'];ai=m['assignment'];assert rec['source_root']==src and rec['source_assignment']==ai
  lows=next(a['lows'] for a in edges[src]['survivors'] if a['assignment']==ai);a=next(a for a in prop[src]['survivors'] if a['assignment']==ai);source=joint[src];ci=source['class'];assert rec['class']==ci;d=dom[ci];root=pack[ci]['survivors'][source['source_root']];S=[]
  for j in root['high3']:
   s=set(d['high3'][j]);S.extend([s,{v^1 for v in s}])
  tau=m['low_tau'];orbits=[(i,tau[i]) for i in range(50) if i<tau[i]];types=[lows[i][1]//2 for i,j in orbits];assert rec['low_orbits']==list(map(list,orbits)) and rec['support_types']==types
  N=[set() for _ in range(70)]
  def edge(i,j):N[i].add(j);N[j].add(i)
  for i,j in d['edges']:edge(i,j)
  for v,s in enumerate(S):
   for r in s:edge(10+v,r)
  for i,j in graphs[source['packing_root']]['survivors'][source['graph']]['edges']:edge(10+i,10+j)
  for i,(v,r) in enumerate(lows):
   edge(20+i,r)
   if v>=0:edge(20+i,10+v)
  for i,j in a['forced_edges']:edge(20+i,20+j)
  possible=[ns.copy() for ns in N]
  for i,j in a['remaining_edges']:possible[20+i].add(20+j);possible[20+j].add(20+i)
  masks=[sum(1<<v for v in ns) for ns in N]
  def allowed(vs):
   if any(masks[v]&masks[w] for v,w in it.combinations(vs,2)):return False
   forced={(i,j) for i,j in it.combinations(range(6),2) if vs[j] in N[vs[i]]}
   if len({x for e in forced for x in e})<2*len(forced):return False
   req={i for i,v in enumerate(vs) if v>=20}
   for pattern in patterns:
    if not forced<=set(pattern) or not req<={v for e in pattern for v in e}:continue
    if all(vs[j] in possible[vs[i]] for i,j in pattern):return True
   return False
  high=[]
  for v in range(0,10,2):
   missing=set(range(5))-{e//2 for e in S[v]};assert len(missing)==2;choices=set()
   for i,j in it.combinations(range(25),2):
    if {types[i],types[j]}==missing and allowed([10+v,11+v]+[20+x for k in [i,j] for x in orbits[k]]):choices.add(frozenset([i,j]))
   assert choices==set(map(frozenset,rec['high_groups'][v//2])) and len(choices)==len(rec['high_groups'][v//2]);high.append(choices);highcount+=len(choices)
  low=set()
  for triple in it.combinations(range(25),3):
   guard()
   if len({types[i] for i in triple})==3 and allowed([20+x for k in triple for x in orbits[k]]):low.add(triple)
  assert low==set(map(tuple,rec['low_groups'])) and len(low)==len(rec['low_groups']);lowcount+=len(low)
 assert (highcount,lowcount)==(1730,23867);status='COMPLETE'
except TimeoutError:pass
first={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'high_options':highcount,'low_options':lowcount};(o/'stage1.json').write_text(json.dumps(first,indent=2)+'\n');print(first,flush=True)
assert status=='COMPLETE'
start=time.monotonic();status='INCOMPLETE';npos=nneg=0
try:
 cr={r['root']:r for r in cover['records']};assert len(cr)==len(cover['records'])==41 and cr.keys()==lookup.keys()
 for key,rec in cr.items():
  guard();d=lookup[key];assert rec['status']=='COMPLETE';w=rec['witness']
  if w is None:assert any(not opts for opts in d['high_groups']);nneg+=1;continue
  high,low=w;assert len(high)==5 and {i for i,m in high}==set(range(5)) and len(low)==5
  used=set()
  for i,m in high:
   chosen=frozenset(j for j in range(25) if m&(1<<j));assert chosen in set(map(frozenset,d['high_groups'][i])) and not chosen&used;used|=chosen
  for m in low:
   chosen=frozenset(j for j in range(25) if m&(1<<j));assert chosen in set(map(frozenset,d['low_groups'])) and not chosen&used;used|=chosen
  assert used==set(range(25));npos+=1
 assert (nneg,npos)==(2,39);status='COMPLETE'
except TimeoutError:pass
second={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'negative':nneg,'witnesses':npos};(o/'stage2.json').write_text(json.dumps(second,indent=2)+'\n');(o/'audit.json').write_text(json.dumps({'hashes':nh,'stages':[first,second]},indent=2)+'\n');print(second)
