from pathlib import Path
import json,hashlib
src=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n78-five-orbit-single-attachment');out=Path(__file__).resolve().parent;pins={}
for mf in ['pins.json','input-pins.json']:
 for n,h in json.loads((src/mf).read_text()).items():
  p=src/n;assert hashlib.sha256(p.read_bytes()).hexdigest()==h;pins[str(p)]=h
  if mf=='input-pins.json' and p.name=='pins.json':
   for name,digest in json.loads(p.read_text()).items():
    q=p.parent/name;assert hashlib.sha256(q.read_bytes()).hexdigest()==digest;pins[str(q)]=digest
for r in json.loads((out/'premise-states.json').read_text()):assert r['status']=='resolved' and r['resolution'].startswith('PASS')
base=Path('/tmp/erdos85-sol1-q9-n78-four-orbit-order24-parameters');gs=json.loads((base/'groups.json').read_text());rs=json.loads((base/'results.json').read_text())['records'];saved=json.loads((src/'central-involutions.json').read_text());omitted=[i for i,r in enumerate(rs) if not r['cubic_sets']];assert omitted==[r['group'] for r in saved] and len(omitted)==9
checks=0
for r in saved:
 m=gs[r['group']]['multiplication'];ivs=[x for x in range(1,24) if m[x][x]==0];assert ivs==r['involutions']
 for x in ivs:
  for g in range(24):
   assert tuple(m[x][m[g][y]] for y in range(24))==tuple(m[g][m[x][y]] for y in range(24));checks+=1
qs=json.loads(Path('/tmp/erdos85-sol1-q9-n78-five-orbit-quotients/results.json').read_text())['cases'];q=next(r for r in qs if r['order']==24 and r['sizes']==[6,12,12,24,24]);single=[m for m in q['quotients'] if m[0]==[1,0,0,4,4]];assert len(single)==8
for m in single:
 assert sorted(m[3][1:3])==[1,2] and m[4][1:3]==list(reversed(m[3][1:3]))
 assert m[3][3]==m[4][4] and m[3][4]==m[4][3]==5-m[3][3] and m[3][3] in (1,2,3,4)
r={'verified_digests':len(pins),'omitted_models':omitted,'central_involution_commutation_checks':checks,'single_attachment_quotients':len(single),'remaining_group_models':15,'scope':'Independent finite table and quotient sanity checks supporting paper cover; no graph enumeration.'}
(out/'input-pins.json').write_text(json.dumps(pins,indent=2)+'\n');(out/'verification.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
