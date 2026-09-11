"""Audit saved F15 receipts without invoking host generation."""
from pathlib import Path
import json,gzip,hashlib,ctypes,importlib.util,time,collections
P=Path(__file__).parent;N=P.parent/'h7-host-prefix-native-verifier';C=P.parent/'h7-host-receipt-cover-verifier'
def main():
 assert not (P/'verification.json').exists(),'Do not overwrite verification evidence'
 for f,h in json.loads((P/'prepared-pins.json').read_text()).items():assert hashlib.sha256((P/f).read_bytes()).hexdigest()==h
 with gzip.open(P/'inputs.jsonl.gz','rt') as f:inputs=[json.loads(line) for line in f]
 assert len(inputs)==4536;summary=json.loads((P/'results.json').read_text());start=time.monotonic();sources={r['global_index']:r for r in inputs}
 sp=importlib.util.spec_from_file_location('cover',C/'cover.py');cv=importlib.util.module_from_spec(sp);sp.loader.exec_module(cv)
 lib=ctypes.CDLL(str(N/'verify.dylib'));lib.star_count.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.c_int,ctypes.POINTER(ctypes.c_uint64)];lib.star_count.restype=ctypes.c_int;lib.verify_prefixes.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.POINTER(ctypes.c_int),ctypes.POINTER(ctypes.c_int),ctypes.POINTER(ctypes.c_uint64),ctypes.c_int,ctypes.POINTER(ctypes.c_uint64)];lib.verify_prefixes.restype=ctypes.c_int
 seen=[];survivors=[];prefixes=domains=rows=structural=negative=0;counts=collections.Counter();unknown=[];nodes=ctypes.c_uint64();E=list(range(42,49));Ea=(ctypes.c_int*7)(*E)
 for shard in summary['shards']:
  with gzip.open(P/shard,'rt') as f:
   for line in f:
    assert time.monotonic()-start<60,'receipt verification60s cap'
    r=json.loads(line);gid=r['global_index'];seen.append(gid);assert gid==inputs[len(seen)-1]['global_index'];src=sources[gid]
    for k in ['completion_index','singleton_index','colouring_index']:assert r[k]==src[k]
    cert=r['receipt'];assert cert['status'] in ['COMPLETE','UNKNOWN'] and cert['nodes']<=100001 and cert['empty_vertices']==E;g=src['neighbors'];counts[cert['status']]+=1
    structural+=cv.check(g,cert)['nodes'];masks=[sum(1<<v for v in ns) for ns in g];a=(ctypes.c_uint64*49)(*masks)
    if cert['prunes']:
     order=(ctypes.c_int*7)(*cert['order']);flat=[v for p in cert['prunes'] for v in [p['depth'],p['singleton'],*p['chosen']]]
     assert lib.verify_prefixes(a,Ea,order,(ctypes.c_uint64*len(flat))(*flat),len(cert['prunes']),ctypes.byref(nodes))==0
    prefixes+=len(cert['prunes'])
    if cert['status']=='UNKNOWN':unknown.append(gid)
    else:negative+=not cert['solutions']
    for j,chosen in enumerate(cert['solutions']):
     full=masks[:]
     for e,m in zip(E,chosen):
      full[e]|=m
      while m:
       bit=m&-m;m-=bit;full[bit.bit_length()-1]|=1<<e
     ga=(ctypes.c_uint64*49)(*full)
     for s in range(7,21):
      n=lib.star_count(ga,s,ctypes.byref(nodes));assert n>0;domains+=1;rows+=n
     survivors.append([gid,j])
 assert len(seen)==summary['visited'] and 4536-len(seen)==summary['unvisited'] and dict(counts)==summary['counts'] and prefixes==summary['prunes'] and len(survivors)==summary['leaves'] and unknown==summary['unknown']
 assert survivors==json.loads((P/'survivors.json').read_text())
 out=dict(status='PASS',visited=len(seen),counts=dict(counts),unvisited=4536-len(seen),unknown=unknown,negative_complete_highs=negative,prunes=prefixes,survivors=len(survivors),structural_nodes=structural,survivor_domains=domains,survivor_rows=rows,native_subset_nodes=nodes.value,seconds=time.monotonic()-start,scope='Independent structural coverage for COMPLETE receipts, exact saved prefix and survivor domain checks. UNKNOWN/unvisited preserved; no residual family check.')
 (P/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
if __name__=='__main__':main()
