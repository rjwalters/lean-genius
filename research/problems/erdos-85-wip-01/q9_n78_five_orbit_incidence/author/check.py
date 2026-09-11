import itertools,json,pathlib,time
start=time.monotonic();out=pathlib.Path(__file__).parent
result={}
for m in range(1,49):
    if 48%m:continue
    sizes=[d for d in range(1,m+1) if m%d==0 and m//d<=8]
    parts=[p for p in itertools.combinations_with_replacement(sizes,5) if sum(p)==78]
    if parts:result[m]=parts
assert result=={24:[(3,3,24,24,24),(6,12,12,24,24)],48:[(6,6,6,12,48),(6,8,8,8,48),(6,8,16,24,24),(6,12,12,24,24),(6,16,16,16,24)]}
assert time.monotonic()-start<30
(out/'results.json').write_text(json.dumps({'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'partitions':result},indent=2)+'\n')
