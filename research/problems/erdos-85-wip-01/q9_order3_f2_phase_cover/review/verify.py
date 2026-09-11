from pathlib import Path
import json,hashlib,math,time,collections
p=Path('/tmp/erdos85-sol1-q9-order3-f2-phase-cover');out=Path(__file__).parent;start=time.monotonic()
def read(f):return json.loads(f.read_text())
pins=read(p/'pins.json')
for f,h in pins.items():assert hashlib.sha256((p/f).read_bytes()).hexdigest()==h,f
ip=read(p/'input-pin.json');assert hashlib.sha256(Path(ip['path']).read_bytes()).hexdigest()==ip['sha256']
states=read(Path(ip['path']));expected={};allowed_by_root={}
for si,s in enumerate(states):
 edges=[(1,2),(4,5)]+[(a,b+3) for a,b in enumerate(s['mapping']) if b>=0]
 partial=[set() for _ in range(6)];closing=[]
 for ei,(a,b) in enumerate(edges):
  reached={a};todo=[a]
  for v in todo:
   for w in partial[v]:
    if w not in reached:reached.add(w);todo.append(w)
  if b in reached:closing.append(ei)
  partial[a].add(b);partial[b].add(a)
 assert len(closing)<=1
 for voltage in ([1,2] if closing else [0]):
  shifts={}
  for ei,(a,b) in enumerate(edges):
   d=voltage if ei in closing else 0
   shifts[a,b]=d;shifts[b,a]=(-d)%3
  masks=[]
  for a in range(3):
   for b in range(3):
    reserved=[(shifts[a,m]+shifts[m,b+3])%3 for m in range(6) if (a,m) in shifts and (m,b+3) in shifts]
    assert len(reserved)==len(set(reserved))
    masks.append(sum(1<<v for v in range(3) if v not in reserved))
  assert [m.bit_count() for m in masks]==sum(s['capacities'],[])
  allowed_by_root[si,voltage]=masks
  for ti,T in enumerate(s['tables']):expected[si,ti,voltage]=math.prod(math.comb(m.bit_count(),n) for m,n in zip(masks,sum(T,[])))
rows=read(p/'phase-parameters.json');seen=set();counts=collections.Counter()
for row in rows:
 assert len(row)==12 and all(type(v)==int for v in row)
 key=tuple(row[:3]);assert key in expected and tuple(row) not in seen;seen.add(tuple(row));counts[key]+=1
 si,ti,voltage=key
 for mask,n,allowed in zip(row[3:],sum(states[si]['tables'][ti],[]),allowed_by_root[si,voltage]):
  assert 0<=mask<8 and mask.bit_count()==n and mask|allowed==allowed
assert dict(counts)==expected
saved=read(p/'counts.json');assert len(saved)==len(expected) and {tuple(r[:3]):r[3] for r in saved}==expected
assert len(rows)==sum(expected.values())==56916 and len(expected)==856
assert len({(si,ti) for si,ti,v in expected})==672
result={'status':'PASS','pins_verified':len(pins),'tables':672,'voltage_roots':len(expected),'valid_unique_parameters':len(rows),'seconds':time.monotonic()-start,'solver_calls':0,'method':'Directed modular two-step voltage sums, independent BFS cycle detection, valid unique records plus product cardinality prove full Cartesian coverage.'}
(out/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
(out/'input-pins.json').write_text(json.dumps({str(p/'pins.json'):hashlib.sha256((p/'pins.json').read_bytes()).hexdigest(),ip['path']:ip['sha256']},indent=2)+'\n')
