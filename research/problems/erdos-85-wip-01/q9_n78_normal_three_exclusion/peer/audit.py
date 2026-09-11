from pathlib import Path
import json,hashlib
p=Path(__file__).resolve().parent;src=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n78-normal-three-exclusion');pins={}
def check(mf):
 for n,h in json.loads(mf.read_text()).items():
  f=mf.parent/n;assert hashlib.sha256(f.read_bytes()).hexdigest()==h,str(f);pins[str(f)]=h
for n in ['pins.json','input-pins.json']:check(src/n)
for n in json.loads((src/'input-pins.json').read_text()):check(Path(n))
states=json.loads((p/'premise-states.json').read_text());assert len(states)==4 and all(r['status']=='resolved' and r['resolution'].startswith('PASS') for r in states)
base=Path('/tmp/erdos85-sol1-q9-n78-central-klein-incidence');graphs=json.loads((base/'results.json').read_text());cap=Path('/tmp/erdos85-sol1-q9-n78-central-klein-edge-capacity');results=json.loads((cap/'results.json').read_text());certs=json.loads((cap/'certificates.json').read_text());assert graphs['status']==results['status']=='COMPLETE'
domain={(r['action'],i):s['adjacency'] for r in graphs['records'] for i,s in enumerate(r['survivors'])};keys=[(r['action'],r['solution']) for r in results['records']];ckeys=[(r['action'],r['solution']) for r in certs];assert len(keys)==len(set(keys))==len(ckeys)==len(set(ckeys))==384 and set(keys)==set(ckeys)==set(domain)
assert all(r['status']=='COMPLETE' and not r['survives'] for r in results['records'])
paths=0
for cert in certs:
 adj=list(map(set,domain[(cert['action'],cert['solution'])]));assert len(adj)==78 and list(map(len,adj))==[9]*42+[4]*36
 assert all(v not in adj[v] and all(v in adj[u] for u in adj[v]) for v in range(78))
 v=cert['blocked_vertex'];assert v==42 and not(adj[v]&set(range(42,78)))
 witnesses=cert['three_edge_paths'];assert len(witnesses)==35 and {w[-1] for w in witnesses}==set(range(43,78))
 for w in witnesses:
  assert len(w)==len(set(w))==4 and w[0]==v and all(b in adj[a] for a,b in zip(w,w[1:]));paths+=1
assert paths==13440
r={'status':'PASS','verified_payloads':len(pins),'fresh_pass_components':4,'exact_partial_root_bijection':384,'independently_verified_paths':paths,'blocked_vertex_each_root':42}
(p/'verification.json').write_text(json.dumps(r,indent=2)+'\n');(p/'input-pins.json').write_text(json.dumps(pins,indent=2)+'\n');print(json.dumps(r))
