from pathlib import Path
import json,gzip,hashlib,itertools,ctypes,time,sqlite3
O=Path(__file__).parent;P=Path('/Users/rwalters/lean-genius-q7-outside-first-20260910/h7-a7-f9-residual-pass');B=P.parent/'h7-a7-f9-host-pass';S=P.parent/'h7-a7-noncycle-singleton-projection';H=P.parent/'h7-a7-f9-projection-extension';N=O.parent/'h7-residual-native-review-rows';assert not (O/'results.json').exists()
inputs=[P/f for f in ['results.json','source-leaves.jsonl.gz','source-indices.json','receipts-000.jsonl.gz','premises.json','run.py','export.py','filter.cpp','batch.cpp','batch.dylib']]+[B/'receipts-000.jsonl.gz',B/'survivors.json',B/'pins.json',S/'results.json',S/'completion-results.json',H/'high-results.json',N/'rows.cpp',N/'rows.dylib'];pins={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs};(O/'input-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
for root in [B,S,H]:
 for f,h in json.loads((root/'pins.json').read_text()).items():assert hashlib.sha256((root/f).read_bytes()).hexdigest()==h
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row
for old in json.loads((P/'premises.json').read_text()):
 live=dict(c.execute('select * from review_requests where id=?',(old['id'],)).fetchone());assert live==old and live['status']=='resolved' and live['resolution'].startswith('PASS')
# Exact host export independent of driver conversion.
original={}
for line in gzip.open(B/'receipts-000.jsonl.gz','rt'):
 r=json.loads(line)
 for j,hosts in enumerate(r['receipt']['solutions']):original[r['case_index'],r['pairing_index'],j]=hosts
exported={}
for line in gzip.open(P/'source-leaves.jsonl.gz','rt'):
 r=json.loads(line)
 for item in r['items']:
  key=r['case_index'],item['pairing_index'],item['leaf_index'];assert key not in exported;exported[key]=[m<<21 for m in item['hosts']]
assert original==exported and len(original)==99224
indices=json.loads((P/'source-indices.json').read_text());assert indices==json.loads((B/'survivors.json').read_text()) and list(map(list,original))==indices
cover=json.loads((S/'results.json').read_text());done=json.loads((S/'completion-results.json').read_text());highs=json.loads((H/'high-results.json').read_text());edges={(r['source_index'],j):es for r in done['results'] if r['F_index']==9 and r['status']=='COMPLETE' for j,es in enumerate(r['solutions'])}
lib=ctypes.CDLL(str(N/'rows.dylib'));lib.enumerate_rows.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.c_int,ctypes.POINTER(ctypes.c_uint64),ctypes.POINTER(ctypes.c_uint64)];lib.enumerate_rows.restype=ctypes.c_int;nodes=ctypes.c_uint64();buffer=(ctypes.c_uint64*1024)();start=time.monotonic();seen=[];ndom=nrows=rowneg=arcneg=batches=removedcount=maxnodes=0;cache={};active=list(range(7,42));K=list(itertools.combinations(range(7),2))
for line in gzip.open(P/'receipts-000.jsonl.gz','rt'):
 assert time.monotonic()-start<60,'review60s cap'
 record=json.loads(line);key=record['case_index'],record['pairing_index'],record['leaf_index'];seen.append(list(key));assert seen[-1]==indices[len(seen)-1];ci,pi,li=key
 if (ci,pi) not in cache:
  hr=highs['results'][ci];sk=hr['source_index'],hr['singleton_index'];rep=cover['representatives'][sk[0]];g=[0]*49
  def add(u,v):g[u]|=1<<v;g[v]|=1<<u
  ren=lambda u:u+42 if u<7 else u
  for u,v in rep['F_edges']+edges[sk]:add(ren(u),ren(v))
  for s,hs in enumerate(rep['singleton_hosts'],7):
   for e in hs:add(s,42+e)
  for p,(u,v) in enumerate(K,21):add(p,u);add(p,v)
  for h,d in enumerate(hr['pairings'][pi]):add(h,14+h);add(h,7+d)
  cache={(ci,pi):g}
 g=cache[ci,pi][:]
 for e,m in enumerate(original[key],42):
  g[e]|=m
  while m:
   bit=m&-m;m-=bit;g[bit.bit_length()-1]|=1<<e
 a=(ctypes.c_uint64*49)(*g);before=nodes.value
 def rows(u):
  global ndom,nrows
  assert u in active;n=lib.enumerate_rows(a,u,buffer,ctypes.byref(nodes));assert n>=0;result=set(buffer[:n]);assert len(result)==n;ndom+=1;nrows+=n;return result
 receipt=record['receipt'];assert receipt['nodes']<=100000
 if receipt['status']=='INFEASIBLE_ROW':assert not rows(receipt['empty_vertex']);rowneg+=1
 else:
  assert receipt['status']=='INFEASIBLE_ARC';D={u:rows(u) for u in active};assert all(D.values())
  assert set(map(int,receipt['initial']))==set(active)
  for u in active:assert len(receipt['initial'][str(u)])==len(D[u]) and set(receipt['initial'][str(u)])==D[u]
  for event in receipt['events']:
   u,v=event['vertex'],event['against'];rm=event['removed'];assert u in D and v in D and u!=v and rm and len(set(rm))==len(rm) and set(rm)<=D[u]
   for row in rm:
    assert all(bool(row>>v&1)!=bool(other>>u&1) or ((g[u]|row)&(g[v]|other)).bit_count()>1 for other in D[v]);removedcount+=1
   D[u]-=set(rm);batches+=1
  assert receipt['empty_vertex'] in D and not D[receipt['empty_vertex']];arcneg+=1
 local=nodes.value-before;assert local<=100000;maxnodes=max(maxnodes,local)
assert seen==indices and rowneg==97540 and arcneg==1684
summary=json.loads((P/'results.json').read_text());assert summary['visited']==99224 and summary['unvisited']==0 and not summary['retained'] and summary['counts']=={'INFEASIBLE_ROW':rowneg,'INFEASIBLE_ARC':arcneg}
for f,h in pins.items():assert hashlib.sha256(Path(f).read_bytes()).hexdigest()==h
out=dict(status='PASS',cases=len(seen),ROW=rowneg,ARC=arcneg,domains=ndom,rows=nrows,arc_batches=batches,failed_support_rows=removedcount,independent_subset_nodes=nodes.value,max_nodes_per_graph=maxnodes,seconds=time.monotonic()-start,scope='Exact accepted2124host leaves and ordered residual endpoints. Independent increasing-active-index row regeneration and complete atomic ARC event replay. All99224negative, no retained/unvisited. Closure join awaits frozen source review.')
(O/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
