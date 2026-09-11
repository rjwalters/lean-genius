import collections,ctypes,gzip,json,pathlib,time
P=pathlib.Path(__file__).parent;S=pathlib.Path('/tmp/erdos85-sol1-h7-a6-f12-host-pass')
def main():
 summary=json.loads((P/'results.json').read_text());host_summary=json.loads((S/'results.json').read_text())
 with gzip.open(S/'inputs.jsonl.gz','rt') as f:inputs={r['global_index']:[sum(1<<v for v in ns) for ns in r['neighbors']] for r in map(json.loads,f)}
 hosts={}
 for shard in host_summary['shards']:
  with gzip.open(S/shard,'rt') as f:
   for line in f:
    r=json.loads(line);hosts[r['global_index']]=(r['receipt']['empty_vertices'],r['receipt']['solutions'])
 expected=json.loads((P/'input-survivors.json').read_text());assert expected==json.loads((S/'survivors.json').read_text())
 lib=ctypes.CDLL(str(P/'subsets.dylib'));U=ctypes.c_uint64;I=ctypes.c_int
 lib.verify_domain.argtypes=[ctypes.POINTER(U),I,ctypes.POINTER(U),I,I,ctypes.c_double,ctypes.POINTER(I)];lib.verify_domain.restype=I
 start=time.monotonic();seen=[];counts=collections.Counter();domains=rows=nodes=batches=failures=0;maxnodes=0
 for shard in summary['shards']:
  with gzip.open(P/shard,'rt') as f:
   for line in f:
    r=json.loads(line);gid,j=r['global_index'],r['leaf_index'];seen.append([gid,j]);cert=r['receipt'];counts[cert['status']]+=1
    if cert['status']=='UNKNOWN':continue # Preserve, never re-search a capped leaf.
    g=list(inputs[gid]);E,leaves=hosts[gid];assert 0<=j<len(leaves)
    for e,m in zip(E,leaves[j]):
     g[e]|=m
     while m:
      bit=m&-m;g[bit.bit_length()-1]|=1<<e;m-=bit
    active={v for v in range(7,49) if g[v]&127}
    if cert['status']=='INFEASIBLE_ROW':wanted={cert['empty_vertex']:[]}
    else:
     assert cert['status'] in ['INFEASIBLE_ARC','ARC_FEASIBLE'];wanted={int(u):rs for u,rs in cert['initial'].items()};assert set(wanted)==active
    gm=(U*49)(*g);used=I()
    for u,rs in wanted.items():
     assert u in active and len(rs)==len(set(rs))
     assert lib.verify_domain(gm,u,(U*len(rs))(*rs),len(rs),100000,60-(time.monotonic()-start),ctypes.byref(used))==1,(gid,j,u,used.value)
     domains+=1;rows+=len(rs)
    nodes+=used.value;maxnodes=max(maxnodes,used.value)
    if cert['status']!='INFEASIBLE_ROW':
     current={u:set(rs) for u,rs in wanted.items()}
     for event in cert['events']:
      u,v=event['vertex'],event['against'];removed=event['removed'];assert u!=v and len(removed)==len(set(removed)) and set(removed)<=current[u]
      for a in removed:
       for b in current[v]:assert ((a>>v)&1)!=((b>>u)&1) or ((g[u]|a)&(g[v]|b)).bit_count()>1
       failures+=1
      current[u]-=set(removed);batches+=1
     if cert['status']=='INFEASIBLE_ARC':assert not current[cert['empty_vertex']]
     else:assert current=={int(u):set(rs) for u,rs in cert['remaining'].items()} and all(current.values())
    assert time.monotonic()-start<60
 assert seen==expected[:len(seen)] and len(seen)==summary['visited'] and len(expected)-len(seen)==summary['unvisited'] and dict(counts)==summary['counts']
 out=dict(status='PASS',visited=len(seen),unvisited_preserved=summary['unvisited'],counts=dict(counts),domains=domains,rows=rows,nodes=nodes,max_nodes=maxnodes,batches=batches,failed_support_rows=failures,seconds=time.monotonic()-start)
 (P/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
if __name__=='__main__':main()
