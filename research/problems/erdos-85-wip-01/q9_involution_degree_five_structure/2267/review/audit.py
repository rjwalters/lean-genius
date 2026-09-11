from pathlib import Path
import json,hashlib,itertools
p=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-involution-n80-residual-five-t2-followup')
pins=json.loads((src/'pins.json').read_text())
for f,h in pins.items():assert hashlib.sha256((src/f).read_bytes()).hexdigest()==h
for f,h in json.loads((src/'input-pins.json').read_text()).items():assert hashlib.sha256(Path(f).read_bytes()).hexdigest()==h
r=json.loads((src/'results.json').read_text());out=[]
res={(0,1)}|{(0,j) for j in (2,4,6,8)}|{(1,j) for j in (3,5,7,9)}|{(2,4),(3,5),(6,8),(7,9)}
for regime,e in r['two_group_results'].items():
 w=e['first_witness'];edges={tuple(sorted(x)) for x in w['edges']};assert len(edges)==len(w['edges'])==51
 G=[set() for _ in range(24)]
 for a,b in edges:assert 0<=a<b<24;G[a].add(b);G[b].add(a)
 assert [len(x) for x in G]==[5,5]+[4]*20+[6,6]
 assert all(len(G[a]&G[b])<=1 for a,b in itertools.combinations(range(24),2))
 tau=[i^1 for i in range(22)]+[22,23]
 assert all({tau[j] for j in G[i]}==G[tau[i]] for i in range(24))
 expected=set(res)
 for name,delta,center in [('left',0,22),('right',6,23)]:
  data=w[name]
  for a,b in data['attachment']:expected.add(tuple(sorted((a+delta,b))))
  for a,b in data['internal']:expected.add(tuple(sorted((a+delta,b+delta))))
  expected|={(i+delta,center) for i in range(10,16)}
  assert len(data['attachment'])==8
  assert sorted(b for a,b in data['attachment'])==list(range(2,10))
  internal_degree=[sum(a==i or b==i for a,b in data['internal']) for i in range(10,16)]
  assert internal_degree==([0,0,1,1,1,1] if regime=='internal_missing' else [1]*6)
 expected|={tuple(sorted(x)) for x in w['cross']};assert expected==edges
 assert sorted(a for a,b in w['cross'])==(list(range(10,16)) if regime=='internal_missing' else list(range(12,16)))
 assert sorted(b for a,b in w['cross'])==(list(range(16,22)) if regime=='internal_missing' else list(range(18,22)))
 out.append({'regime':regime,'vertices':24,'edges':51,'codegree_pairs':276,'witness_verified':True})
assert 32**2*48==49152 and 56**2*8==25088
(p/'results.json').write_text(json.dumps({'source_pins':pins,'witnesses':out,'search_replayed':False,'survivor_counts_independently_recomputed':False},indent=2)+'\n')
print('PASS two explicit witnesses,552 codegrees,exact matching regimes; no enumeration replay')
