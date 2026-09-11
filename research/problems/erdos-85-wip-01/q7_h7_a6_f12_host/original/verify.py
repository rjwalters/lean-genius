import array,collections,ctypes,gzip,json,pathlib,time
import cover
P=pathlib.Path(__file__).parent
lib=ctypes.CDLL(str(P/'prefix.dylib'));U=ctypes.c_uint64;I=ctypes.c_int
lib.verify_prefixes.argtypes=[ctypes.POINTER(U),ctypes.POINTER(I),ctypes.POINTER(I),ctypes.POINTER(U),I,ctypes.POINTER(U)];lib.verify_prefixes.restype=I
lib.star_count.argtypes=[ctypes.POINTER(U),I,ctypes.POINTER(U)];lib.star_count.restype=I
def main():
 summary=json.loads((P/'results.json').read_text())
 with gzip.open(P/'inputs.jsonl.gz','rt') as f:inputs=[json.loads(line) for line in f]
 records=[]
 for name in summary['shards']:
  with gzip.open(P/name,'rt') as f:records.extend(json.loads(line) for line in f)
 assert len(records)==summary['visited'] and len(inputs)-len(records)==summary['unvisited']
 start=time.monotonic();counts=collections.Counter();survivors=[];total_nodes=prefixes=leaves=structural_nodes=0;max_nodes=0
 for source,record in zip(inputs,records):
  assert all(source[k]==record[k] for k in ['global_index','completion_index','singleton_index','colouring_index'])
  receipt=record['receipt'];base=source['neighbors'];check=cover.check(base,receipt,max_nodes=100000,seconds=60-(time.monotonic()-start))
  counts[receipt['status']]+=1;structural_nodes+=check['nodes'];E=receipt['empty_vertices'];order=receipt['order'];g=[sum(1<<v for v in ns) for ns in base];gm=(U*49)(*g);nodes=U()
  if receipt['prunes']:
   flat=array.array('Q',(v for p in receipt['prunes'] for v in [p['depth'],p['singleton']]+p['chosen']));assert flat.itemsize==8
   assert lib.verify_prefixes(gm,(I*7)(*E),(I*7)(*order),(U*len(flat)).from_buffer(flat),len(receipt['prunes']),ctypes.byref(nodes))==0
  prefixes+=len(receipt['prunes'])
  S=[s for s in range(7,49) if (g[s]&127).bit_count()==1]
  for j,ms in enumerate(receipt['solutions']):
   full=list(g)
   for e,m in zip(E,ms):
    full[e]|=m
    while m:
     bit=m&-m;p=bit.bit_length()-1;full[p]|=1<<e;m-=bit
   gg=(U*49)(*full)
   for s in S:assert lib.star_count(gg,s,ctypes.byref(nodes))>0
   survivors.append([record['global_index'],j]);leaves+=1
  local=nodes.value+check['nodes'];assert local<=100000 and time.monotonic()-start<60
  total_nodes+=nodes.value;max_nodes=max(max_nodes,local)
 assert dict(counts)==summary['counts'] and prefixes==summary['prunes'] and leaves==summary['leaves']
 assert survivors==json.loads((P/'survivors.json').read_text())
 out=dict(status='PASS',visited=len(records),unvisited_preserved=summary['unvisited'],counts=dict(counts),prefixes=prefixes,leaves=leaves,direct_star_nodes=total_nodes,structural_nodes=structural_nodes,max_combined_nodes=max_nodes,seconds=time.monotonic()-start)
 (P/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
if __name__=='__main__':main()
