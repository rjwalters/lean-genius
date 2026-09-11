from pathlib import Path
import importlib.util,json,ctypes,time
P=Path(__file__).parent;A=Path('/tmp/erdos85-sol1-h7-monotone-pair-host-api');lib=ctypes.CDLL(str(P/'rows.dylib'));lib.enumerate_rows.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.c_int,ctypes.POINTER(ctypes.c_uint64),ctypes.POINTER(ctypes.c_uint64)];lib.enumerate_rows.restype=ctypes.c_int;nodes=ctypes.c_uint64();out=(ctypes.c_uint64*1024)();start=time.monotonic();ndom=nrows=fixtures=maxrows=0
for family in ['a7','a6']:
 sp=importlib.util.spec_from_file_location('ref_'+family,A/f'reference_{family}.py');m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
 for adj in json.loads((A/f'fixtures_{family}.json').read_text()):
  assert time.monotonic()-start<60;g,support,E,U=m.validate(adj);expected=m.complete_domains(g,support,U,m.Budget(100000,time.monotonic()+60));assert expected['status']=='DOMAINS_COMPLETE';a=(ctypes.c_uint64*49)(*g)
  for u in U:
   n=lib.enumerate_rows(a,u,out,ctypes.byref(nodes));assert n>=0 and len(set(out[:n]))==n and set(out[:n])==set(expected['initial'][u]),(family,fixtures,u,n)
   ndom+=1;nrows+=n;maxrows=max(maxrows,n)
  fixtures+=1
r=dict(status='PASS',fixtures=fixtures,domains=ndom,rows=nrows,max_rows=maxrows,independent_subset_nodes=nodes.value,seconds=time.monotonic()-start,scope='Exact independent increasing-active-index domain enumeration versus accepted a6/a7 reference on45existing fixtures. No residual family searched.')
(P/'test-results.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
