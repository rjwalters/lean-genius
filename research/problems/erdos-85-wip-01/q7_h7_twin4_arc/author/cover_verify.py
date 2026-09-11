import pathlib,json,itertools,collections,time,functools
P=pathlib.Path(__file__).parent;r=json.loads((P/'profile-source.json').read_text())['results'][0]
assert r['status']=='COMPLETE' and len(r['assignments'])==4458
sd=json.loads((P/'seed-source.json').read_text());base=list(map(set,next(s['adjacency'] for s in sd['patterns'] if s['twins_adjacent'])));H=sorted(base[0]);es=list(itertools.combinations(range(1,7),2));pc=r['profile']['pair_counts'];domains=[]
for h,n in zip(H,pc):
 allowed={c for c in range(1,7) if not base[h]&base[c]};opts=[]
 for selected in itertools.combinations(range(15),n):
  endpoints=[c for e in selected for c in es[e]]
  if len(set(endpoints))==len(endpoints) and set(endpoints)<=allowed:opts.append(sum(1<<e for e in selected))
 domains.append(opts)
# Forward squarefree coefficient product, no author symmetry pruning.
start=time.monotonic();states=0;coeff={0:1}
for options in domains:
 out=collections.defaultdict(int)
 for used,count in coeff.items():
  states+=1
  if states>100000 or time.monotonic()-start>60:raise TimeoutError
  for m in options:
   if not used&m:out[used|m]+=count
 coeff=out
assert set(coeff)=={32767}
# Eight explicit actions permute and flip matched pairs(1,2),(3,4).
actions=[]
for pairs in itertools.permutations([(1,2),(3,4)]):
 for flips in itertools.product([0,1],repeat=2):
  vals=sum((list(pair[::-1] if flip else pair) for pair,flip in zip(pairs,flips)),[])+[5,6]
  cp=dict(zip(range(1,7),vals));hp=[0,1]+[cp[c]+1 for c in range(1,7)];em=[es.index(tuple(sorted((cp[a],cp[b])))) for a,b in es];actions.append((hp,em))
seen=set();hist=collections.Counter()
for a in r['assignments']:
 orbit=set()
 for hp,em in actions:
  b=[0]*8
  for h,m in enumerate(a):b[hp[h]]=sum(1<<em[e] for e in range(15) if m>>e&1)
  assert all(m in domains[h] for h,m in enumerate(b)) and functools.reduce(int.__or__,b)==32767 and sum(m.bit_count() for m in b)==15
  orbit.add(tuple(b))
 assert not seen&orbit;seen|=orbit;hist[len(orbit)]+=1
assert len(seen)==coeff[32767]
result=dict(status='COMPLETE',coefficient_states=states,raw_count=coeff[32767],orbit_union=len(seen),representatives=len(r['assignments']),orbit_histogram=dict(hist),seconds=time.monotonic()-start)
(P/'cover-verification.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
