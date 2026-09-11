from pathlib import Path
import itertools as it,json,hashlib,time
p=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n78-normal-three-character')
for manifest in ['pins.json','input-pins.json']:
 for n,h in json.loads((src/manifest).read_text()).items():
  f=Path(n) if Path(n).is_absolute() else src/n
  assert hashlib.sha256(f.read_bytes()).hexdigest()==h
G=json.loads(Path('/tmp/erdos85-sol1-q9-n78-four-orbit-order24-parameters/groups.json').read_text())[:22];expected=json.loads((src/'results.json').read_text())['groups'];start=time.monotonic();records=[]
try:
 for gi,g in enumerate(G):
  if time.monotonic()-start>30:raise TimeoutError
  m=g['multiplication'];orders=[]
  for x in range(24):
   power=0
   for k in range(1,25):
    power=m[power][x]
    if power==0:orders.append(k);break
  elems=[x for x in range(1,24) if orders[x] in [2,4,8]];subs={frozenset([0])}
  for k in [1,2,3]:
   for gens in it.combinations(elems,k):
    H={0};todo=[0]
    for a in todo:
     for b in gens:
      z=m[a][b]
      if z not in H:H.add(z);todo.append(z)
     if len(H)>8:break
    if len(H) in [2,4,8]:subs.add(frozenset(H))
  assert len(subs)==expected[gi]['subgroups']
  target=[78 if x==0 else 0 if orders[x]%3==0 else 6 for x in range(24)];chars={}
  for H in subs:
   cosets={frozenset(m[a][h] for h in H) for a in range(24)}
   vector=tuple(sum(frozenset(m[x][v] for v in C)==C for C in cosets) for x in range(24))
   if all(a<=b for a,b in zip(vector,target)):chars.setdefault(vector,set()).add(tuple(sorted(H)))
  saved={tuple(c['values']):{tuple(H) for H in c['subgroups']} for c in expected[gi]['characters']};assert chars==saved
  vectors=sorted(chars);solutions=[]
  for choice in it.combinations_with_replacement(range(len(vectors)),7):
   if time.monotonic()-start>30:raise TimeoutError
   if sum(vectors[i][0] for i in choice)!=78:continue
   if all(sum(vectors[i][x] for i in choice)==target[x] for x in range(1,24)):solutions.append(choice)
  assert set(solutions)==set(map(tuple,expected[gi]['solutions']))
  records.append(dict(group=gi,name=g['name'],subgroups=len(subs),characters=len(chars),solutions=solutions,orbit_sizes=[sorted(vectors[i][0] for i in s) for s in solutions]))
 status='COMPLETE'
except TimeoutError:status='UNKNOWN'
result=dict(status=status,cap_seconds=30,seconds=time.monotonic()-start,verified=len(records),records=records)
p.joinpath('audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='records'}));print([(r['group'],len(r['solutions'])) for r in records])
