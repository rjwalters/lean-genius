import pathlib,json,itertools,collections,hashlib,time
P=pathlib.Path(__file__).parent;R=pathlib.Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/twin6-census-review');src=pathlib.Path('/tmp/erdos85-sol1-h7-profile-partitions/remaining-results.json')
for f,h in json.loads((R/'pins.json').read_text()).items():assert hashlib.sha256((R/f).read_bytes()).hexdigest()==h
r=next(r for r in json.loads(src.read_text())['results'] if r['twins_adjacent'] and r['profile_index']==6)
es=list(itertools.combinations(range(1,7),2));pc=[2,1,2,2,2,2,2,2];assert pc==r['profile']['pair_counts']
# Explicit twin matching: S0a-S0b, P01-P02,P03-P04,P05-P06.
forbidden=[None,None,2,1,4,3,6,5];domains=[]
for h,n in enumerate(pc):
 allowed=[i for i,e in enumerate(es) if forbidden[h] not in e]
 domains.append([sum(1<<i for i in chosen) for chosen in itertools.combinations(allowed,n) if len({v for i in chosen for v in es[i]})==2*n])
# Iterative squarefree coefficient multiplication, forward host order.
coeff={0:1};states=0;start=time.monotonic()
for domain in domains:
 nxt=collections.defaultdict(int)
 for used,n in coeff.items():
  states+=1
  if states>100000 or time.monotonic()-start>60:raise TimeoutError
  for m in domain:
   if not m&used:nxt[used|m]+=n
 coeff=nxt
assert dict(coeff)=={32767:125280}
# Explicit wreath-product48actions, no exhaustive permutation search.
actions=[]
for pairs in itertools.permutations([(1,2),(3,4),(5,6)]):
 for flips in itertools.product([0,1],repeat=3):
  values=sum((list(pair[::-1] if f else pair) for pair,f in zip(pairs,flips)),[]);cp=dict(zip(range(1,7),values));hp=[0,1]+[cp[c]+1 for c in range(1,7)];em=[es.index(tuple(sorted((cp[a],cp[b])))) for a,b in es];actions.append((hp,em))
seen=set();hist=collections.Counter()
for a in r['assignments']:
 orbit=set()
 for hp,em in actions:
  b=[0]*8
  for h,m in enumerate(a):b[hp[h]]=sum(1<<em[e] for e in range(15) if m>>e&1)
  assert all(m in domains[h] for h,m in enumerate(b)) and sum(b)==32767
  orbit.add(tuple(b))
 assert not seen&orbit;seen|=orbit;hist[len(orbit)]+=1
assert len(seen)==125280 and len(r['assignments'])==2640
out=dict(status='PASS',forward_coefficient_states=states,raw_count=coeff[32767],orbit_union=len(seen),histogram=dict(hist),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),seconds=time.monotonic()-start)
(P/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
