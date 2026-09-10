from pathlib import Path
import json,itertools,hashlib,collections
p=Path(__file__).parent;src=Path('/tmp/erdos85-sol1-h7-pair-host-reduction/results.json');sd=Path('/tmp/erdos85-sol1-h7-high0-cover/results.json');d=json.loads(src.read_text());seeds=json.loads(sd.read_text())['patterns'];out=[]
for row in d['results']:
 seed=next(s for s in seeds if s['twins_adjacent']==row['twins_adjacent']);hosts=row['hosts'];idx={v:i for i,v in enumerate(hosts)};matching={tuple(sorted((idx[a],idx[b]))) for a,b in seed['local_edges']};actions=[]
 for high in itertools.permutations(range(2,8)):
  for perm in [(0,1)+high,(1,0)+high]:
   if {tuple(sorted((perm[a],perm[b]))) for a,b in matching}==matching:actions.append(perm)
 maxp=row['pair_max'];minp=row['pair_min'];caps=[a-b for a,b in zip(maxp,minp)];assert caps==[2,2,1,1,1,1,1,1] and sum(maxp)==18
 profiles=[x for x in itertools.product(*(range(n+1) for n in caps)) if sum(x)==3];assert len(profiles)==70
 orbits=collections.Counter()
 for x in profiles:
  images=[]
  for perm in actions:
   y=[0]*8
   for i,v in enumerate(x):y[perm[i]]=v
   images.append(tuple(y))
  key=min(images);orbits[key]+=1
 assert sum(orbits.values())==70
 reps=[]
 for defect,size in sorted(orbits.items()):
  pairs=[m-z for m,z in zip(maxp,defect)];empties=[x-delta for x,delta in zip(pairs,row['offsets'])]
  assert sum(pairs)==15 and sum(empties)==7
  reps.append(dict(defects=defect,pair_counts=pairs,empty_counts=empties,orbit_size=size))
 out.append(dict(twins_adjacent=row['twins_adjacent'],stabilizer_size=len(actions),labelled_profiles=70,profile_orbits=len(orbits),representatives=reps));print({k:v for k,v in out[-1].items() if k!='representatives'},flush=True)
(p/'results.json').write_text(json.dumps(dict(source_pins={str(src):hashlib.sha256(src.read_bytes()).hexdigest(),str(sd):hashlib.sha256(sd.read_bytes()).hexdigest()},results=out,scope='Necessary pair/empty host-count profile quotient only; no pair-colouring census or exclusion of any profile.'),indent=2)+'\n')
