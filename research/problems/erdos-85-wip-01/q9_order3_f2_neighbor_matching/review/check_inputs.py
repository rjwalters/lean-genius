from pathlib import Path
import json,hashlib
src=Path('/tmp/erdos85-sol1-q9-order3-f2-neighbor-matching');out=Path(__file__).parent
pins=json.loads((src/'pins.json').read_text())
for n,h in pins.items():assert hashlib.sha256((src/n).read_bytes()).hexdigest()==h,n
ips=json.loads((src/'input-pins.json').read_text())
for n,h in ips.items():assert hashlib.sha256(Path(n).read_bytes()).hexdigest()==h,n
params=json.loads(Path('/tmp/erdos85-sol1-q9-order3-f2-phase-cover/phase-parameters.json').read_text());states=json.loads(Path('/tmp/erdos85-sol1-q9-order3-f2-contingency/receipts.json').read_text());cache={}
lines=(src/'inputs.txt').read_text().splitlines();assert len(lines)==len(params)==56916
for index,(line,param) in enumerate(zip(lines,params)):
 si,ti,voltage,*masks=param;state=states[si]
 if (si,voltage) not in cache:
  es=[(1,2),(4,5)]+[(a,b+3) for a,b in enumerate(state['mapping']) if b>=0];tree=[set() for _ in range(6)];adj=[set() for _ in range(18)]
  for a,b in es:
   seen={a};queue=[a]
   for u in queue:
    for v in tree[u]:
     if v not in seen:seen.add(v);queue.append(v)
   shift=voltage if b in seen else 0
   tree[a].add(b);tree[b].add(a)
   for g in range(3):
    u=3*a+g;v=3*b+(g+shift)%3;adj[u].add(v);adj[v].add(u)
  cache[si,voltage]=[sum(1<<v for v in nb) for nb in adj]
 endpoints=[]
 for cell,mask in enumerate(masks):
  a,b=divmod(cell,3)
  for shift in range(3):
   if mask&(1<<shift):endpoints.extend((3*a,3*b+shift))
 if state['cross_orbits']==3:
  if state['missing_labels'] is None:endpoints.extend((-1,-1))
  else:a,b=state['missing_labels'];endpoints.extend((3*a,-1,-1,3*b))
 assert list(map(int,line.split()))==[index,*cache[si,voltage],*endpoints]
receipts=[list(map(int,l.split())) for l in (src/'receipts.txt').read_text().splitlines()];assert receipts==[[i,-1] for i in range(56916)]
(out/'input-verification.json').write_text(json.dumps({'status':'PASS','source_pins':len(pins),'external_pins':len(ips),'records_reconstructed':len(lines),'receipts':len(receipts)},indent=2)+'\n')
(out/'input-pins.json').write_text(json.dumps({str(src/'pins.json'):hashlib.sha256((src/'pins.json').read_bytes()).hexdigest(),**ips},indent=2)+'\n');print('PASS all56916 inputs and coverage receipts independently reconstructed')
