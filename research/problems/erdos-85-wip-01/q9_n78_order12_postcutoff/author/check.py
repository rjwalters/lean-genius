from pathlib import Path
import json,sqlite3,hashlib,time
p=Path(__file__).parent;start=time.monotonic();case=json.loads((p/'case-map.json').read_text());roots=set(case['group_cover']+[case['prior_order_bound'],2553,2555,2544])
roots.update(case['groups']['S3xC2'])
for row in case['groups']['A4']:
 roots.update(row.get('cover',[]))
 for b in row['branches']:roots.update(b['reviews'])
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row;queue=sorted(roots);states={};hashes={};edges=[]
while queue:
 rid=queue.pop()
 if rid in states:continue
 r=dict(c.execute('select * from review_requests where id=?',(rid,)).fetchone());accepted=r['status']=='resolved' and r['resolution'].startswith('PASS');states[rid]=dict(status=r['status'],accepted=accepted,resolution=r['resolution'],refs=json.loads(r['refs']))
 for ref in json.loads(r['refs']):
  pins=Path(ref);payload=json.loads(pins.read_text());hashes[str(pins)]=hashlib.sha256(pins.read_bytes()).hexdigest()
  for n,h in payload.items():
   f=Path(n) if Path(n).is_absolute() else pins.parent/n;actual=hashlib.sha256(f.read_bytes()).hexdigest();assert actual==h,(rid,str(f));hashes[str(f)]=actual
  # Pending packets need their own current dependencies accepted too.
  premise=pins.parent/'premise-states.json'
  if not accepted and premise.exists():
   parents=json.loads(premise.read_text())
   if isinstance(parents,list):
    for parent in parents:
     if isinstance(parent,dict) and 'id' in parent:queue.append(parent['id']);edges.append([rid,parent['id']])
assert all(r['accepted'] for r in states.values()), states
for f in [p.parent/'n78-a4-four-orbit-attachment-cover/ERRATUM.json',Path('/tmp/erdos85-sol1-review2602/ERRATUM.md')]:
 hashes[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest()
profiles=sorted((a,b,cc,d) for a in range(27) for b in range(14) for cc in [0,3] for d in range(7) if 3*a+2*b in [2,6] and 3*a+6*b+4*cc+12*d==78)
assert profiles==sorted(tuple(r['profile']) for r in case['groups']['A4'])
assert sorted(case['groups'])==sorted(['C12','Dic12','C3xV4','S3xC2','A4'])
pending=sorted(rid for rid,r in states.items() if not r['accepted']);result=dict(status='DRAFT_PENDING_REVIEW' if pending else 'READY_FOR_COMPOSITION_REVIEW',seconds=time.monotonic()-start,direct_roots=sorted(roots),pending_reviews=pending,review_states=states,dependency_edges=edges,verified_hashes=hashes,accepted_conclusion=False,reason='Even after premises pass, the composition itself requires independent review.');(p/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(status=result['status'],seconds=result['seconds'],direct_roots=len(roots),review_nodes=len(states),verified_hashes=len(hashes),pending_reviews=pending)))
