from pathlib import Path
import itertools,json,hashlib
p=Path(__file__).parent;src=Path('/tmp/erdos85-sol1-q9-elementary-nine-cover/matrices.json'); records=json.loads(src.read_text())
def key(r):return (r['isolated_A'],r['isolated_B'],*(v for row in r['D'] for v in row))
allkeys={key(r) for r in records};assert len(allkeys)==16
maps=[]
for aa in [(1,2),(2,1)]:
 for bb in [(3,4),(4,3)]:
  for cc in itertools.permutations((5,6,7)):maps.append((0,*aa,*bb,*cc))
assert len(set(maps))==24
orbits={};seen=set()
for r in records:
 orb=set()
 for perm in maps:
  d=[[0]*8 for _ in range(8)]
  for i in range(8):
   for j in range(8):d[perm[i]][perm[j]]=r['D'][i][j]
  orb.add((perm[r['isolated_A']],perm[r['isolated_B']],*(v for row in d for v in row)))
 assert orb<=allkeys
 canon=min(orb)
 if canon not in orbits:assert not (orb&seen);seen|=orb;orbits[canon]=orb
assert seen==allkeys
result={'status':'PASS','input_count':16,'group_size':24,'orbits':[{'size':len(o),'isolated_A':k[0],'isolated_B':k[1],'D':[list(k[2+8*i:10+8*i]) for i in range(8)]} for k,o in sorted(orbits.items())]}
(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');(p/'input-pin.json').write_text(json.dumps({'path':str(src),'sha256':hashlib.sha256(src.read_bytes()).hexdigest()},indent=2)+'\n');print(json.dumps(result))
