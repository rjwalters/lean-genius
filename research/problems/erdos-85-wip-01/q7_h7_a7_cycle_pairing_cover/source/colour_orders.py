from pathlib import Path
import json,itertools,hashlib,collections,time
P=Path(__file__).parent;source=P/'results.json';data=json.loads(source.read_text());assert data['status']=='COMPLETE';start=time.monotonic();out=[]
def normalize(order):
 i=order.index(0);x=order[i:]+order[:i];return min(x,(0,)+x[:0:-1])
orders=sorted({normalize(p) for p in itertools.permutations(range(7))});assert len(orders)==360
for case in data['cases']:
 rows=[];raw_count=0;cyclic_examined=0
 for pi,r in enumerate(case['representatives']):
  blocks=list(map(tuple,r['blocks']));bi={b:i for i,b in enumerate(blocks)};actions=set()
  for action in case['aut_R']:
   moved=[tuple(sorted((action[a],action[b]))) for a,b in blocks]
   if set(moved)==set(blocks):actions.add(tuple(bi[b] for b in moved))
  seen=set()
  for order in orders:
   if order in seen:continue
   orbit={normalize(tuple(action[x] for x in order)) for action in actions}
   assert not seen&orbit;seen|=orbit
   representative=min(orbit);raw_orbit=r['orbit_size']*14*len(orbit);raw_count+=raw_orbit
   rows.append({'pairing_index':pi,'block_cycle':representative,'cyclic_orbit_size':len(orbit),'full_labelled_orbit_size':raw_orbit})
  assert len(seen)==360;cyclic_examined+=len(seen)
 assert raw_count==case['raw_partitions']*5040
 out.append({'raw_partitions':case['raw_partitions'],'pairing_representatives':len(case['representatives']),'cyclic_orders_covered':cyclic_examined,'proper_colouring_representatives':len(rows),'raw_labelled_colourings':raw_count,'orbit_histogram':dict(collections.Counter(r['full_labelled_orbit_size'] for r in rows)),'representatives':rows})
r={'status':'COMPLETE','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'cases':out,'seconds':time.monotonic()-start,'scope':'Exact properQedge-colouring cover moduloAut(R)xAut(C7empty), via pairing-orbit then cyclic block-order stabilizer quotient. No singleton incidence or lowgraph completion and no cappedhosttree retry.'}
(P/'colour-results.json').write_text(json.dumps(r,indent=2)+'\n');print([{k:v for k,v in r.items() if k!='representatives'} for r in out])
