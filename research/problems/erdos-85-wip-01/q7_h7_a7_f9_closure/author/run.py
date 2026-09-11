import pathlib,json,gzip,hashlib,sqlite3,importlib.util,argparse,time,ctypes,array,collections
P=pathlib.Path(__file__).parent;S=P.parent/'h7-a7-f9-host-pass';A=pathlib.Path('/tmp/erdos85-sol1-h7-projection-residual-driver');N=pathlib.Path('/tmp/erdos85-sol1-h7-singleton-complete-native-api')
args=argparse.ArgumentParser();args.add_argument('--source-review',type=int,required=True);opts=args.parse_args();assert not (P/'launch.json').exists() and not (P/'results.json').exists(),'No overwrite or retry'
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row;premises=[]
for rid in [2111,2117,2121,opts.source_review]:
 r=dict(c.execute('select * from review_requests where id=?',(rid,)).fetchone());assert r['status']=='resolved' and r['resolution'].startswith('PASS');premises.append(r)
assert str(S) in str(premises[-1]['refs'])
for root in [S,A,N]:
 for f,h in json.loads((root/'pins.json').read_text()).items():assert hashlib.sha256((root/f).read_bytes()).hexdigest()==h
for f in ['batch.cpp','batch.dylib','filter.cpp']:assert (P/f).read_bytes()==(A/f).read_bytes()
assert (P/'filter.cpp').read_bytes()==(N/'filter.cpp').read_bytes();assert (P/'source-pins.json').read_bytes()==(S/'pins.json').read_bytes()
sp=importlib.util.spec_from_file_location('inputs',S/'inputs.py');inputs=importlib.util.module_from_spec(sp);sp.loader.exec_module(inputs);cover,edges,highs=inputs.load();indices=json.loads((P/'source-indices.json').read_text());assert len(indices)==99224
lib=ctypes.CDLL(str(P/'batch.dylib'));lib.native_now.restype=ctypes.c_double;assert abs(lib.native_now()-time.monotonic())<0.1;lib.batch_check.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.POINTER(ctypes.c_uint32),ctypes.c_int,ctypes.c_int,ctypes.c_double];lib.batch_check.restype=ctypes.c_char_p
(P/'premises.json').write_text(json.dumps(premises,indent=2)+'\n');(P/'launch.json').write_text(json.dumps(dict(total=len(indices),max_nodes=100000,aggregate_seconds=60))+'\n');start=time.monotonic();deadline=start+60;counts=collections.Counter();seen=[];retained=[];nodes=0;shards=[];stream=None;size=0
with gzip.open(P/'source-leaves.jsonl.gz','rt') as source:
 for line in source:
  if time.monotonic()>deadline:break
  group=json.loads(line);ci=group['case_index'];r=highs['results'][ci];base49=inputs.base_graph(cover,edges,r);base21=[]
  for u in range(21):
   v=u+42 if u<7 else u;assert all(w>=7 for w in base49[v]);base21.append(sum(1<<(w-42 if w>=42 else w) for w in base49[v]))
  flat=array.array('I',(v for item in group['items'] for chunk in [r['pairings'][item['pairing_index']],item['hosts']] for v in chunk));assert flat.itemsize==4
  receipts=json.loads(lib.batch_check((ctypes.c_uint64*21)(*base21),(ctypes.c_uint32*len(flat)).from_buffer(flat),len(group['items']),100000,deadline));assert len(receipts)<=len(group['items'])
  for item,receipt in zip(group['items'],receipts):
   assert receipt['status'] in ['INFEASIBLE_ROW','INFEASIBLE_ARC','ARC_FEASIBLE','UNKNOWN'];key=[ci,item['pairing_index'],item['leaf_index']];seen.append(key);counts[receipt['status']]+=1;nodes+=receipt['nodes']
   if receipt['status'] in ['ARC_FEASIBLE','UNKNOWN']:retained.append(key+[receipt['status']])
   record=dict(case_index=ci,pairing_index=key[1],leaf_index=key[2],receipt=receipt);blob=gzip.compress((json.dumps(record,separators=(',',':'))+'\n').encode(),mtime=0);assert len(blob)<50000000
   if stream is None or size+len(blob)>50000000:
    if stream is not None:stream.close()
    name=f'receipts-{len(shards):03d}.jsonl.gz';shards.append(name);stream=(P/name).open('wb');size=0
   stream.write(blob);size+=len(blob)
if stream is not None:stream.close()
assert seen==indices[:len(seen)];result=dict(total=len(indices),visited=len(seen),unvisited=len(indices)-len(seen),counts=dict(counts),nodes=nodes,retained=retained,receipt_shards=shards,seconds=time.monotonic()-start)
(P/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
