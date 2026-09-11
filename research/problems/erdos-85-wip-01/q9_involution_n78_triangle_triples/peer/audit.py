from pathlib import Path
import json,hashlib,itertools,collections
src=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/involution-n78-triangle-triples');out=Path(__file__).parent
pins=json.loads((src/'pins.json').read_text())
for name,h in pins.items():assert hashlib.sha256((src/name).read_bytes()).hexdigest()==h
premise=json.loads((src/'premise.json').read_text());assert hashlib.sha256(Path(premise['source']).read_bytes()).hexdigest()==premise['sha256']
roots=set()
for perm in itertools.permutations(range(6)):
 if any(perm[x^1]!=(perm[x]^1) for x in range(6)):continue
 if sum(perm[i]>perm[j] for i in range(6) for j in range(i+1,6))%2:roots.add(perm)
assert len(roots)==24
r=json.loads((src/'results.json').read_text());entries=r['roots']
assert len(entries)==24 and {tuple(e['pi']) for e in entries}==roots
for e in entries:
 assert e['status']=='WITNESS'
 reps=e['witness_orbits'];assert len(reps)==15 and all(t[0]%2==0 for t in reps)
 triples=[tuple(x^flip for x in t) for t in reps for flip in (0,1)]
 assert len(set(triples))==30 and all(len(t)==3 and all(0<=x<6 for x in t) for t in triples)
 for a,b in [(0,1),(0,2),(1,2)]:
  expected={(x,y) for x in range(6) for y in range(6) if y!=(e['pi'][x] if (a,b)==(1,2) else x)}
  actual=collections.Counter((t[a],t[b]) for t in triples)
  assert set(actual)==expected and set(actual.values())=={1}
 for col in range(3):assert collections.Counter(t[col] for t in triples)==dict.fromkeys(range(6),5)
assert sum(e['nodes'] for e in entries)==525 and max(e['nodes'] for e in entries)==53
(out/'results.json').write_text(json.dumps({'roots_independently_enumerated':24,'witnesses_verified':24,'expanded_triples':720,'pair_projections_verified':2160,'source_pins':pins,'premise':premise,'search_replayed':False},indent=2)+'\n')
print('PASS: all24 roots,720 triples,2160 projected pairs independently verified; no search replay.')
