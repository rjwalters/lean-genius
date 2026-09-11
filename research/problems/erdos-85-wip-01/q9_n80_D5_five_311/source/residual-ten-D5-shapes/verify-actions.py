from pathlib import Path
import json,itertools as it,time
p=Path(__file__).resolve().parent;start=time.monotonic();data=json.loads((p/'results.json').read_text());seen=set();counts=[]
for c in data['classes']:
 orbit=set()
 for perm in it.permutations(range(5)):
  for flips in it.product((0,1),repeat=5):
   assert time.monotonic()-start<30
   f=[2*perm[i]+(t^flips[i]) for i in range(5) for t in [0,1]]
   orbit.add(tuple(sorted(tuple(sorted((f[u],f[v]))) for u,v in c['representative'])))
 expected={tuple(map(tuple,r['edges'])) for r in data['records'] if r['key']==c['key']}
 assert orbit==expected and not orbit&seen;seen|=orbit;counts.append(len(orbit))
assert len(seen)==len(data['records'])
out={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'maps_per_class':3840,'orbit_sizes':counts,'covered_graphs':len(seen)};(p/'actions.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
