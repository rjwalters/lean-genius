from pathlib import Path
import json,hashlib,sqlite3,time,gzip
from incidence import enumerate_incidences
P=Path(__file__).parent;S=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/h7-a7-cycle-pairing-cover')
db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
for rid in [2097,2102]:
 r=db.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert r and r[0]=='resolved' and r[1].startswith('PASS'),('unaccepted prerequisite',rid)
pins=json.loads((P/'input-pins.json').read_text())
for f,h in pins.items():assert hashlib.sha256(Path(f).read_bytes()).hexdigest()==h
pairings=json.loads((S/'results.json').read_text())['cases'];colourings=json.loads((S/'colour-results.json').read_text())['cases'];F={tuple(sorted((i,(i+1)%7))) for i in range(7)};start=time.monotonic();deadline=start+60;summary=[]
with gzip.open(P/'incidences.jsonl.gz','wt') as stream:
 for ci,(base,colours) in enumerate(zip(pairings,colourings)):
  visited=positive=solutions=nodes=0
  for i,r in enumerate(colours['representatives']):
   if time.monotonic()>deadline:break
   pairing=base['representatives'][r['pairing_index']]['blocks'];phi={}
   for x,block_id in enumerate(r['block_cycle']):
    for edge_id in pairing[block_id]:phi[tuple(base['Q_edges'][edge_id])]=x
   result=enumerate_incidences(phi,F);assert result['nodes']<=3280<100000
   codes=result['solutions'];visited+=1;positive+=bool(codes);solutions+=len(codes);nodes+=result['nodes']
   stream.write(json.dumps({'R_case':ci,'colouring_index':i,'solutions':codes,'nodes':result['nodes']},separators=(',',':'))+'\n')
  summary.append({'R_case':ci,'total':len(colours['representatives']),'visited':visited,'unvisited':len(colours['representatives'])-visited,'positive_colourings':positive,'negative_colourings':visited-positive,'singleton_incidence_choices':solutions,'nodes':nodes})
status='COMPLETE' if all(r['unvisited']==0 for r in summary) else 'UNKNOWN'
r={'status':status,'cases':summary,'seconds':time.monotonic()-start,'scope':'Exact singleton incidence lists on the accepted F=C7 propercolouring representatives. Propercolouring zeros only; no wholeR/F/H7 or remaininglowedge completion, no oldcappedhosttree retry. Any unvisited colourings remain unresolved.'}
(P/'summary.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
