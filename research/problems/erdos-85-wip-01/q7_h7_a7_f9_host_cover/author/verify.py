import pathlib,json,gzip,time,ctypes,array,collections
from inputs import load,base_graph,given_high
import cover_reference
P=pathlib.Path(__file__).parent;lib=ctypes.CDLL(str(P/'verify.dylib'));U=ctypes.c_uint64;I=ctypes.c_int;lib.verify_prefix_batch.argtypes=[ctypes.POINTER(U),ctypes.POINTER(I),ctypes.POINTER(U),ctypes.POINTER(I),I];lib.verify_prefix_batch.restype=I

def endpoints(base,E,chosen,codes):
 flat=array.array('Q',(m for row in chosen for m in row));assert flat.itemsize==8
 return lib.verify_prefix_batch((U*49)(*[sum(1<<v for v in ns) for ns in base]),(I*7)(*E),(U*len(flat)).from_buffer(flat),(I*len(codes))(*codes),len(codes))
old=P.parent/'h7-singleton-complete-row-api';fixtures=json.loads((old/'fixtures.json').read_text());certs=json.loads((old/'receipts.json').read_text());fixed=badtests=0
for adj,cert in zip(fixtures,certs):
 base=list(map(set,adj));E=list(range(42,49));chosen=[]
 for e in E:
  ps=base[e]&set(range(21,42));chosen.append(sum(1<<p for p in ps))
  for p in ps:base[e].remove(p);base[p].remove(e)
 s=next((s for s in range(7,21) if not cert['initial'][str(s)]),None);code=ord('.') if s is None else ord('A')+s-7
 assert endpoints(base,E,[chosen],[code])==0;fixed+=1
 positive=next(s for s in range(7,21) if cert['initial'][str(s)]);assert endpoints(base,E,[chosen],[ord('A')+positive-7])==1;badtests+=1
cover,es,highs=load();results=json.loads((P/'results.json').read_text());expected=[(r['case_index'],pi) for r in highs['results'] for pi in range(len(r['pairings']))];assert len(expected)==28336 and results['visited']==results['total']==28336 and results['unvisited']==0 and not results['unknown_high_graphs']
start=time.monotonic();deadline=start+60;seen=[];survivors=[];counts=collections.Counter();nprunes=nleaves=structural=negative=0;cache={}
for shard in results['receipt_shards']:
 with gzip.open(P/shard,'rt') as stream:
  for line in stream:
   assert time.monotonic()<deadline
   record=json.loads(line);ci,pi=record['case_index'],record['pairing_index'];seen.append((ci,pi));r=highs['results'][ci];assert (record['source_index'],record['singleton_index'])==(r['source_index'],r['singleton_index'])
   if ci not in cache:cache[ci]=base_graph(cover,es,r)
   base=given_high(cache[ci],r['pairings'][pi]);cert=record['receipt'];assert cert['status']=='COMPLETE' and 0<cert['nodes']<=100000
   structure=cover_reference.check(base,cert,max_nodes=100000,seconds=max(0,deadline-time.monotonic()));assert structure['coverage_proved'];structural+=structure['nodes']
   E=cert['empty_vertices'];assert E==list(range(42,49));chosen=[];codes=[]
   for prune in cert['prunes']:
    s=prune['singleton'];assert 7<=s<=20;chosen.append(prune['chosen']);codes.append(ord('A')+s-7)
   for j,leaf in enumerate(cert['solutions']):chosen.append(leaf);codes.append(ord('.'));survivors.append([ci,pi,j])
   assert endpoints(base,E,chosen,codes)==0,(ci,pi)
   nprunes+=len(cert['prunes']);nleaves+=len(cert['solutions']);negative+=not cert['solutions'];counts[cert['status']]+=1
assert seen==expected and survivors==json.loads((P/'survivors.json').read_text());assert nprunes==results['pruned_prefixes'] and nleaves==results['surviving_host_leaves'] and negative==results['negative_high_graphs']
r=dict(status='PASS',given_high_graphs=len(seen),prunes=nprunes,surviving_leaves=nleaves,negative_high_graphs=negative,structural_nodes=structural,fixed_endpoint_tests=fixed,false_endpoint_rejections=badtests,seconds=time.monotonic()-start,scope='Exact local matching/unique-P prefix coverage plus direct reconstructed singleton-star endpoint verification; entire F9 high input list. No residual-edge exclusion.')
(P/'verification.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
