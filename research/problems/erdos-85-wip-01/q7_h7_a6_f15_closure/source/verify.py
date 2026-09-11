"""Independent row regeneration and propagation replay; no residual search."""
from pathlib import Path
import json,gzip,hashlib,ctypes,time,collections
P=Path(__file__).parent;S=P.parent/'h7-a6-f15-host-pass';N=P.parent/'h7-residual-native-review-rows'
def main():
 assert not (P/'verification.json').exists(),'No overwrite verification'
 for f,h in json.loads((P/'prepared-pins.json').read_text()).items():assert hashlib.sha256((P/f).read_bytes()).hexdigest()==h
 for f,h in json.loads((S/'pins.json').read_text()).items():assert hashlib.sha256((S/f).read_bytes()).hexdigest()==h
 original={}
 for shard in json.loads((S/'results.json').read_text())['shards']:
  for line in gzip.open(S/shard,'rt'):
   r=json.loads(line)
   if r['receipt']['solutions']:original[r['global_index']]=r['receipt']['solutions']
 exported={r['global_index']:r['hosts'] for r in map(json.loads,gzip.open(P/'source-leaves.jsonl.gz','rt'))};assert exported==original
 indices=json.loads((P/'source-indices.json').read_text());assert indices==json.loads((S/'survivors.json').read_text()) and len(indices)==142812
 bases={r['global_index']:[sum(1<<v for v in ns) for ns in r['neighbors']] for r in map(json.loads,gzip.open(P/'source-bases.jsonl.gz','rt'))};summary=json.loads((P/'results.json').read_text())
 lib=ctypes.CDLL(str(N/'rows.dylib'));lib.enumerate_rows.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.c_int,ctypes.POINTER(ctypes.c_uint64),ctypes.POINTER(ctypes.c_uint64)];lib.enumerate_rows.restype=ctypes.c_int;buffer=(ctypes.c_uint64*1024)();nodes=ctypes.c_uint64();start=time.monotonic();seen=[];retained=[];counts=collections.Counter();ndom=nrows=batches=failed=maxnodes=0;active=set(range(7,42))
 for shard in summary['shards']:
  for line in gzip.open(P/shard,'rt'):
   assert time.monotonic()-start<60,'verification60s cap'
   r=json.loads(line);gid,li=r['global_index'],r['leaf_index'];seen.append([gid,li]);assert seen[-1]==indices[len(seen)-1];g=bases[gid][:]
   for e,m in enumerate(original[gid][li],42):
    g[e]|=m
    while m:
     bit=m&-m;m-=bit;g[bit.bit_length()-1]|=1<<e
   a=(ctypes.c_uint64*49)(*g);before=nodes.value
   def rows(u):
    nonlocal ndom,nrows
    assert u in active;n=lib.enumerate_rows(a,u,buffer,ctypes.byref(nodes));assert n>=0;out=set(buffer[:n]);assert len(out)==n;ndom+=1;nrows+=n;return out
   cert=r['receipt'];status=cert['status'];assert status in ['INFEASIBLE_ROW','INFEASIBLE_ARC','ARC_FEASIBLE','UNKNOWN'];counts[status]+=1
   if status=='INFEASIBLE_ROW':assert not rows(cert['empty_vertex'])
   else:
    initial={int(u):rs for u,rs in cert.get('initial',{}).items()};assert set(initial)<=active
    if status!='UNKNOWN':assert set(initial)==active
    D={u:rows(u) for u in initial}
    for u,rs in initial.items():assert len(rs)==len(D[u]) and set(rs)==D[u]
    for event in cert.get('events',[]):
     u,v=event['vertex'],event['against'];rm=event['removed'];assert u in D and v in D and u!=v and rm and len(rm)==len(set(rm)) and set(rm)<=D[u]
     for row in rm:
      assert all(bool(row>>v&1)!=bool(other>>u&1) or ((g[u]|row)&(g[v]|other)).bit_count()>1 for other in D[v]);failed+=1
     D[u]-=set(rm);batches+=1
    if status=='INFEASIBLE_ARC':assert not D[cert['empty_vertex']]
    if status in ['ARC_FEASIBLE','UNKNOWN']:retained.append([gid,li,status])
   local=nodes.value-before;assert local<=100000;maxnodes=max(maxnodes,local)
 assert seen==indices[:len(seen)] and len(seen)==summary['visited'] and len(indices)-len(seen)==summary['unvisited'] and dict(counts)==summary['counts'] and retained==summary['retained']
 out=dict(status='PASS',visited=len(seen),unvisited=len(indices)-len(seen),counts=dict(counts),retained=retained,domains=ndom,rows=nrows,arc_batches=batches,failed_support_rows=failed,independent_subset_nodes=nodes.value,max_nodes_per_graph=maxnodes,seconds=time.monotonic()-start,scope='Exact accepted host-export/source join and independent complete row regeneration/atomic ARC replay. UNKNOWN/feasible/unvisited remain unresolved; no retry.')
 (P/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
if __name__=='__main__':main()
