from pathlib import Path
import json,hashlib,collections
p=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-involution-n80-t01-incidence');base=src.parent/'q9-involution-n80-degree-five-centers'
pins=json.loads((src/'pins.json').read_text())
for f,h in pins.items():assert hashlib.sha256((src/f).read_bytes()).hexdigest()==h
for f,h in json.loads((src/'input-pins.json').read_text()).items():assert hashlib.sha256(Path(f).read_bytes()).hexdigest()==h
cases=json.loads((base/'results.json').read_text())['retained'];graphs=json.loads((base/'representatives.json').read_text());r=json.loads((src/'results.json').read_text());roots=r['results'];assert len(roots)==48
assert [(e['t'],e['case']) for e in roots]==[(t,c) for t in (0,1) for c in cases]
assert [e['status'] for e in roots]==['WITNESS']*25+['UNKNOWN']+['UNVISITED']*22
assert sum(e['nodes'] for e in roots)==r['total_nodes']==500000
assert all(0<=e['nodes']<=100000 for e in roots) and r['elapsed']<30
checked=0
for e in roots:
 if e['status']!='WITNESS':assert e['witness'] is None;continue
 t=e['t'];case=e['case'];P=set(case['P']);H=[set() for _ in range(10)]
 for a,b in graphs[case['graph_index']]['edges']:H[a].add(b);H[b].add(a)
 Y=e['witness'];assert len(Y)==10 and all(len(row)==5 and all(x in (0,1) for x in row) for row in Y)
 Q=[[int(i==0 or j==0 or (t==1 and {i,j}=={1,2})) for j in range(5)] for i in range(5)]
 assert [sum(Y[f][j] for f in range(10)) for j in range(5)]==[6]+[3 if t and j in (1,2) else 2 for j in range(1,5)]
 for f in range(10):
  delta=2-sum(Y[f]);assert delta in (0,1,2) and Y[f][0]==int(f not in P) and len(H[f]&P)<=1+delta
  for j in range(5):assert sum(Y[h][j] for h in H[f])<=sum(Y[f][k]*Q[k][j] for k in range(5))+delta;checked+=1
assert checked==1250
(p/'results.json').write_text(json.dumps({'source_pins':pins,'roots':48,'positive_witnesses':25,'unknown':1,'unvisited':22,'nodes':500000,'inequalities_checked':checked,'search_replayed':False},indent=2)+'\n')
print('PASS25 exact witnesses/1250 inequalities;1UNKNOWN22UNVISITED preserved; no replay')
