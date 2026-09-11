from pathlib import Path
import json,ctypes,importlib.util,time
P=Path(__file__).parent;start=time.monotonic();sp=importlib.util.spec_from_file_location('direct',P.parent/'h7-monotone-host-prefix-verifier/verify.py');direct=importlib.util.module_from_spec(sp);sp.loader.exec_module(direct)
lib=ctypes.CDLL(str(P/'verify.dylib'));lib.star_count.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.c_int,ctypes.POINTER(ctypes.c_uint64)];lib.star_count.restype=ctypes.c_int
lib.verify_prefixes.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.POINTER(ctypes.c_int),ctypes.POINTER(ctypes.c_int),ctypes.POINTER(ctypes.c_uint64),ctypes.c_int,ctypes.POINTER(ctypes.c_uint64)];lib.verify_prefixes.restype=ctypes.c_int
arr=lambda g:(ctypes.c_uint64*49)(*[sum(1<<v for v in ns) for ns in g]);nodes=ctypes.c_uint64();ndom=nrows=0
source=Path('/tmp/erdos85-sol1-h7-monotone-pair-host-api');fixtures=[]
for family in ['a7','a6']:fixtures+=json.loads((source/f'fixtures_{family}.json').read_text())
f=json.loads((P.parent/'h7-a6-same-colour-fixture/fixture.json').read_text());g=list(map(set,f['neighbors']));ep=[(e,p) for e in range(7,14) for p in sorted(g[e]) if p>=28]
for e,p in ep:g[e].remove(p);g[p].remove(e);fixtures.append([sorted(ns) for ns in g])
for fixture in fixtures:
 assert time.monotonic()-start<60;g=list(map(set,fixture));a=arr(g)
 for s in range(7,49):
  if len(g[s]&set(range(7)))!=1:continue
  expected=direct.domains(g,s);got=lib.star_count(a,s,ctypes.byref(nodes));assert got==len(expected),(s,got,len(expected));ndom+=1;nrows+=got
f=json.loads((P.parent/'h7-monotone-host-prefix-verifier/fixture.json').read_text());base=f['base'];r=json.loads((P.parent/'review2123/unrestricted-receipt.json').read_text());E=(ctypes.c_int*7)(*r['empty_vertices']);order=(ctypes.c_int*7)(*r['order'])
def prefixcall(prunes):
 flat=[x for p in prunes for x in [p['depth'],p['singleton'],*p['chosen']]];return lib.verify_prefixes(arr(base),E,order,(ctypes.c_uint64*len(flat))(*flat),len(prunes),ctypes.byref(nodes))
assert prefixcall(r['prunes'])==0
bad=dict(f['prune'],singleton=14);assert prefixcall([bad])==1
bad=dict(f['prune'],depth=0);assert prefixcall([bad])==1
bad=dict(f['prune'],chosen=[0]*7);assert prefixcall([bad])==1
out=dict(status='PASS',fixtures=len(fixtures),singleton_domains=ndom,rows=nrows,prunes=len(r['prunes']),bad_prunes_rejected=3,native_subset_nodes=nodes.value,seconds=time.monotonic()-start,scope='Exact native counts versus independent direct49graph stars on all old45 fixtures plus12host-deleted stages;26existing unrestricted-fixture prefixes checked. No family receipts processed.')
(P/'test-results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
