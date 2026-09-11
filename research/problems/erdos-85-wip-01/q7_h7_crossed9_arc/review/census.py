import pathlib,json,itertools,time,hashlib,functools
P=pathlib.Path('/tmp/erdos85-sol1-h7-profile-partitions');O=pathlib.Path(__file__).parent;pins=json.loads((P/'pins.json').read_text());assert all(hashlib.sha256((P/f).read_bytes()).hexdigest()==h for f,h in pins.items())
r=next(x for x in json.loads((P/'remaining-results.json').read_text())['results'] if not x['twins_adjacent'] and x['profile_index']==9);assert r['status']=='COMPLETE';pc=r['profile']['pair_counts'];edges=list(itertools.combinations(range(1,7),2));ei={e:i for i,e in enumerate(edges)};assert edges==list(map(tuple,r['edge_order']))
seed=json.loads(pathlib.Path('/tmp/erdos85-sol1-h7-high0-cover/results.json').read_text())['patterns'][1];assert not seed['twins_adjacent'];hosts=['S0a','S0b']+['P0'+str(c) for c in range(1,7)];local={tuple(sorted((hosts.index(a),hosts.index(b)))) for a,b in seed['local_edges']};mate={a:b for e in local for a,b in [e,e[::-1]]};avail=[set(range(1,7))-({mate[h]-1} if mate[h]>=2 else set()) for h in range(8)]
domains=[]
for h in range(8):
 opts=[]
 for chosen in itertools.combinations(range(15),pc[h]):
  ends=[v for i in chosen for v in edges[i]]
  if len(ends)==len(set(ends)) and set(ends)<=avail[h]:opts.append(sum(1<<i for i in chosen))
 domains.append(opts)
actions=[]
for q in itertools.permutations(range(2,8)):
 for perm in [(0,1)+q,(1,0)+q]:
  if {tuple(sorted((perm[a],perm[b]))) for a,b in local}!=local or any(pc[h]!=pc[perm[h]] for h in range(8)):continue
  em=[ei[tuple(sorted((perm[a+1]-1,perm[b+1]-1)))] for a,b in edges];actions.append((perm,em))
assert len(actions)==2

# Independent exact raw count via fixed reversed-host subset DP, no symmetry pruning.
start=time.monotonic();nodes=0;order=list(reversed(range(8)))
@functools.lru_cache(None)
def count(k,used):
 global nodes
 nodes+=1
 if nodes>100000 or time.monotonic()-start>60:raise TimeoutError
 if k==8:return int(used==32767)
 return sum(count(k+1,used|m) for m in domains[order[k]] if not m&used)
status='COMPLETE'
try:raw=count(0,0)
except TimeoutError:status='UNKNOWN';raw=None
seen=set();sizes=[]
if status=='COMPLETE':
 for groups in r['assignments']:
  assert all(m in domains[h] for h,m in enumerate(groups))
  assert sum(m.bit_count() for m in groups)==15
  assert __import__('functools').reduce(int.__or__,groups)==32767
  orbit=set();tuples=[]
  for perm,em in actions:
   target=[0]*8
   for h,m in enumerate(groups):target[perm[h]]=sum(1<<em[j] for j in range(15) if m>>j&1)
   assert all(m in domains[h] for h,m in enumerate(target))
   tuples.append(tuple(target));orbit.add(sum(m<<(15*h) for h,m in enumerate(target)))
  assert tuple(groups)==min(tuples) and not seen&orbit
  seen|=orbit;sizes.append(len(orbit))
 assert len(seen)==raw and len(sizes)==1920
assert all(hashlib.sha256((P/f).read_bytes()).hexdigest()==h for f,h in pins.items())
out={'status':status,'memoized_count_states':nodes,'raw_count':raw,'source_representatives':len(sizes),'disjoint_orbit_union':len(seen),'orbit_size_histogram':{size:sizes.count(size) for size in sorted(set(sizes))},'seconds':time.monotonic()-start,'pins':pins,'scope':'Independent complete crossed9 census cover: raw reverse-host subset-DP count, valid disjoint full group orbits from1920representatives exhaust exact count. No capped profiles or graph completion run.'}
(O/'census-results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
