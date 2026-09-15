"""Independent raw-source reconstruction, exact export join, and all negative endpoints."""
import collections,ctypes,gzip,hashlib,itertools,json,time
from pathlib import Path
P=Path(__file__).parent
R=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')
S=R/'q7_h7_a6_f13_host/original';A=R/'q7_h7_a6_high_pairing_cover/original';V=R/'q7_h7_a6_f15_closure/source/row-verifier'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for root,manifest in [(S,'final-pins.json'),(A,'pins.json')]:
 for n,h in json.loads((root/manifest).read_text()).items():assert sha(root/n)==h
assert sha(V/'rows.dylib')=='cabf8dbf14dcfed235c764f836bc9b369e9bbac48050da0a0bc4eacb8cf87a4b'
result=json.loads((P/'results.json').read_text());launch=json.loads((P/'launch.json').read_text())
assert sha(P/'run.py')==launch['driver_sha256'] and sha(P/'input-survivors.json')==launch['input_survivors_sha256']
files=[P/'results.json',P/'launch.json',P/'input-survivors.json',S/'final-pins.json',A/'pins.json',V/'rows.cpp',V/'rows.dylib']+[P/n for n in result['shards']]
pins={str(p):sha(p) for p in files}
with (P/'verification-launch.json').open('x') as f:json.dump({'aggregate_seconds':180,'input_pins':pins},f,indent=2)
start=time.monotonic();deadline=start+180
cover=json.loads((A/'source-cover-results.json').read_text());complete=json.loads((A/'source-completion-results.json').read_text());high={}
for line in gzip.open(A/'high-colourings.jsonl.gz','rt'):
 r=json.loads(line)
 if r['F_index']==13:high[r['completion_index'],r['singleton_index']]=r['colourings']
bases={}
for line in gzip.open(S/'inputs.jsonl.gz','rt'):
 r=json.loads(line);ci,j=r['completion_index'],r['singleton_index'];src=complete['results'][ci]
 assert src['F_index']==13 and src['status']=='COMPLETE'
 F=cover['cases'][13];X=F['representatives'][src['X_index']];colour=high[ci,j][r['colouring_index']]
 g=[0]*49
 def add(u,v):g[u]|=1<<v;g[v]|=1<<u
 def ren(v):return v+42 if v<7 else v
 for u,v in F['F_edges']+src['solutions'][j]:add(ren(u),ren(v))
 for s,hs in enumerate(X['singleton_hosts'],7):
  for e in hs:add(s,42+e)
 for s,h in enumerate(colour,7):add(s,h)
 for h in range(3):add(18+h,h)
 for p,hs in enumerate(itertools.combinations(range(7),2),21):
  for h in hs:add(p,h)
 assert g==[sum(1<<v for v in ns) for ns in r['neighbors']]
 assert r['global_index'] not in bases;bases[r['global_index']]=g
 assert time.monotonic()<deadline
assert len(bases)==49065
host=json.loads((S/'results.json').read_text());assignments={};expected=[]
for name in host['shards']:
 for line in gzip.open(S/name,'rt'):
  r=json.loads(line);gid=r['global_index'];h=r['receipt'];assert h['status']=='COMPLETE' and h['empty_vertices']==list(range(42,49))
  assignments[gid]=h['solutions'];expected.extend([gid,j] for j in range(len(h['solutions'])))
assert len(assignments)==49065 and set(assignments)==set(bases)
assert expected==json.loads((S/'survivors.json').read_text())==json.loads((P/'input-survivors.json').read_text()) and len(expected)==1196264
lib=ctypes.CDLL(str(V/'rows.dylib'));U=ctypes.c_uint64
lib.enumerate_rows.argtypes=[ctypes.POINTER(U),ctypes.c_int,ctypes.POINTER(U),ctypes.POINTER(U)];lib.enumerate_rows.restype=ctypes.c_int
buffer=(U*1024)();nodes=U();counts=collections.Counter();visited=ndom=nrows=batches=removed=0;retained=[];active=set(range(7,42))
for name in result['shards']:
 for line in gzip.open(P/name,'rt'):
  record=json.loads(line);gid=record['global_index'];certs=record['receipts'];assert len(certs)<=len(assignments[gid])
  for j,cert in enumerate(certs):
   assert time.monotonic()<deadline and [gid,j]==expected[visited]
   g=bases[gid][:]
   for e,m in enumerate(assignments[gid][j],42):
    g[e]|=m
    while m:
     bit=m&-m;m-=bit;g[bit.bit_length()-1]|=1<<e
   a=(U*49)(*g)
   def rows(u):
    global ndom,nrows
    assert u in active
    n=lib.enumerate_rows(a,u,buffer,ctypes.byref(nodes));assert 0<=n<=1024
    out=set(buffer[:n]);assert len(out)==n;ndom+=1;nrows+=n;return out
   st=cert['status'];counts[st]+=1;visited+=1;before=nodes.value
   if st=='INFEASIBLE_ROW':assert not rows(cert['empty_vertex'])
   elif st=='INFEASIBLE_ARC':
    D={u:rows(u) for u in active};assert all(D.values()) and set(map(int,cert['initial']))==active
    for u in active:assert len(cert['initial'][str(u)])==len(D[u]) and set(cert['initial'][str(u)])==D[u]
    for event in cert['events']:
     u,v=event['vertex'],event['against'];rm=event['removed']
     assert u in D and v in D and u!=v and rm and len(rm)==len(set(rm)) and set(rm)<=D[u]
     for row in rm:
      assert all(bool(row>>v&1)!=bool(other>>u&1) or ((g[u]|row)&(g[v]|other)).bit_count()>1 for other in D[v]);removed+=1
     D[u]-=set(rm);batches+=1
    assert cert['empty_vertex'] in D and not D[cert['empty_vertex']]
   else:
    assert st in ['ARC_FEASIBLE','UNKNOWN'];retained.append([gid,j,st])
   assert nodes.value-before<=100000
assert visited==result['visited'] and len(expected)-visited==result['unvisited'] and dict(counts)==result['counts'] and retained==result['retained']
for n,h in pins.items():assert sha(Path(n))==h
out={'status':'PASS_EXACT_SOURCE_AND_NEGATIVES','source_graphs':len(bases),'host_leaves':len(expected),'visited':visited,'unvisited':result['unvisited'],'counts':dict(counts),'retained':len(retained),'domains':ndom,'rows':nrows,'arc_batches':batches,'failed_support_rows':removed,'independent_subset_nodes':nodes.value,'seconds':time.monotonic()-start,'scope':'Exact raw-source graphs and reviewed host export; all negative endpoints checked. UNKNOWN/positive/suffix not promoted. Upstream source and quotient completeness inherited.'}
(P/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
