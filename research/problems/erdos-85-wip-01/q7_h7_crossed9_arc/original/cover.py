from pathlib import Path
import json,itertools,time,hashlib
p=Path(__file__).parent;src=p/'profile-source.json';hs=Path('/tmp/erdos85-sol1-h7-high0-cover/results.json');rs=Path('/tmp/erdos85-sol1-h7-pair-host-reduction/results.json');row=next(r for r in json.loads(src.read_text())['results'] if not r['twins_adjacent'] and r['profile_index']==9);assert row['status']=='COMPLETE';seed=next(s for s in json.loads(hs.read_text())['patterns'] if not s['twins_adjacent']);reduction=next(s for s in json.loads(rs.read_text())['results'] if not s['twins_adjacent'])
E=list(itertools.combinations(range(1,7),2));index={e:i for i,e in enumerate(E)};available=list(map(set,reduction['available_colours']));counts=row['profile']['pair_counts'];hostindex={h:i for i,h in enumerate(reduction['hosts'])};matching={frozenset([hostindex[a],hostindex[b]]) for a,b in seed['local_edges']};raw=set();nodes=0;start=time.monotonic()
def matchings(remaining,h):
 edges=[e for e in E if e in remaining and set(e)<=available[h]]
 for group in itertools.combinations(edges,counts[h]):
  if len(set(itertools.chain.from_iterable(group)))==2*len(group):yield frozenset(group)
def visit(remaining,assigned):
 global nodes
 nodes+=1
 if nodes>100000 or time.monotonic()-start>60:raise TimeoutError
 if len(assigned)==8:
  assert not remaining;raw.add(tuple(sum(1<<index[e] for e in assigned[h]) for h in range(8)));return
 options=[(h,list(matchings(remaining,h))) for h in range(8) if h not in assigned]
 h,groups=min(options,key=lambda r:(len(r[1]),-r[0]))
 for group in groups:visit(remaining-group,{**assigned,h:group})
status='COMPLETE'
try:visit(frozenset(E),{})
except TimeoutError:status='UNKNOWN'
actions=[]
for labels in itertools.permutations(range(1,7)):
 for swap in [False,True]:
  hp=[1,0] if swap else [0,1];hp+=[1+c for c in labels]
  if {frozenset(hp[i] for i in e) for e in matching}!=matching or any(counts[h]!=counts[hp[h]] for h in range(8)):continue
  em=[index[tuple(sorted((labels[a-1],labels[b-1])))] for a,b in E];actions.append((hp,em))
def transform(assignment,action):
 hp,em=action;out=[0]*8
 for h,m in enumerate(assignment):out[hp[h]]=sum(1<<em[i] for i in range(15) if m>>i&1)
 return tuple(out)
covered=set();orbit_sizes=[]
if status=='COMPLETE':
 for representative in row['assignments']:
  orbit={transform(representative,a) for a in actions};assert orbit<=raw and not orbit&covered;covered|=orbit;orbit_sizes.append(len(orbit))
 assert covered==raw and len(orbit_sizes)==1920
out=dict(status=status,nodes=nodes,raw_assignments=len(raw),stabilizer=len(actions),canonical_representatives_checked=len(orbit_sizes),orbit_size_histogram={str(k):orbit_sizes.count(k) for k in set(orbit_sizes)},seconds=time.monotonic()-start,source_pins={str(f):hashlib.sha256(f.read_bytes()).hexdigest() for f in [src,hs,rs]},scope='Independent dynamic minimum-domain host enumeration WITHOUT symmetry pruning; full orbit sets partition rawdomain exactly into supplied1920representatives. One complete crossed9 domain only; no old UNKNOWN profiles rerun.')
(p/'cover-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
