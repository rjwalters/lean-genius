from pathlib import Path
import json,hashlib
p=Path(__file__).resolve().parent;s=Path('/tmp/erdos85-sol1-q9-elementary-nine-symmetry');pins=json.loads((s/'pins.json').read_text())
for n,h in pins.items():assert hashlib.sha256((s/n).read_bytes()).hexdigest()==h
link=json.loads((s/'input-pin.json').read_text());raw=Path(link['path']).read_bytes();assert hashlib.sha256(raw).hexdigest()==link['sha256'];data=json.loads(raw)
def key(r):return (r['isolated_A'],r['isolated_B'],tuple(x for row in r['D'] for x in row))
def swap(k,a,b):
 A,B,flat=k;perm=list(range(8));perm[a],perm[b]=b,a
 return (perm[A],perm[B],tuple(flat[8*perm[i]+perm[j]] for i in range(8) for j in range(8)))
allkeys=set(map(key,data));assert len(allkeys)==16;used=set();sizes=[]
for r in json.loads((s/'results.json').read_text())['orbits']:
 root=key(r);orbit={root};todo=[root]
 for k in todo:
  for a,b in [(1,2),(3,4),(5,6),(6,7)]:
   v=swap(k,a,b)
   if v not in orbit:orbit.add(v);todo.append(v)
 assert orbit<=allkeys and not(orbit&used) and len(orbit)==r['size'];assert root==min(orbit);used|=orbit;sizes.append(len(orbit))
assert used==allkeys and sorted(sizes)==[4,12]
(p/'results.json').write_text(json.dumps({'status':'PASS','method':'generator closure BFS, four transpositions','input_count':16,'orbit_sizes':sizes,'source_pins':pins},indent=2)+'\n');print('PASS: generator closures have sizes4/12 and exhaust all16 pinned matrices.')
