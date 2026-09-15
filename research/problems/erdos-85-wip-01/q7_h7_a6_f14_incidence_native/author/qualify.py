"""Differential qualification against reviewed Python family and choice models."""
import ctypes,gzip,hashlib,importlib.util,json,time
from pathlib import Path
D=Path(__file__).parent
R=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')
A=Path('/Users/rwalters/lean-genius-h7-a6-f12-weighted-family-sol2-20260915');B=Path('/Users/rwalters/lean-genius-h7-a6-f12-incidence-projection-sol2-20260915')
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for base in [A,B]:
 for n,h in read(base/'pins.json').items():assert sha(base/n)==h,n
mods=[]
for name,path in [('families',A/'probe.py'),('choices',B/'probe.py')]:
 sp=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);mods.append(m)
lib=ctypes.CDLL(str(D/'projection.dylib'));U=ctypes.c_uint64
lib.check_projection.argtypes=[ctypes.POINTER(U),ctypes.c_int,ctypes.c_double];lib.check_projection.restype=ctypes.c_char_p;lib.projection_now.restype=ctypes.c_double
assert abs(lib.projection_now()-time.monotonic())<.1
fixtures=[];source_pins={}
for source in [12,14]:
 if source==12:
  P=R/'q7_h7_a6_f12_host/original';I=P;wanted=[(r['global_index'],r['leaf_index']) for r in read(B/'results.json')['records']]
 else:
  I=Path('/Users/rwalters/lean-genius-h7-a6-f14-sol1-20260915');P=I/'hosts';keys=read(P/'survivors.json');wanted=[tuple(keys[i*(1757882-1)//127]) for i in range(128)]
 ids={gid for gid,j in wanted};ins={r['global_index']:r['neighbors'] for r in map(json.loads,gzip.open(I/'inputs.jsonl.gz','rt')) if r['global_index'] in ids};hosts={}
 for name in read(P/'results.json')['shards']:
  for r in map(json.loads,gzip.open(P/name,'rt')):
   if r['global_index'] in ids:hosts[r['global_index']]=r['receipt']['solutions']
 source_pins[str(P/'results.json')]=sha(P/'results.json');source_pins[str(I/'inputs.jsonl.gz')]=sha(I/'inputs.jsonl.gz')
 for gid,j in wanted:
  g=[sum(1<<v for v in ns) for ns in ins[gid]]
  for e,mask in enumerate(hosts[gid][j],42):
   g[e]|=mask
   for v in range(49):
    if mask>>v&1:g[v]|=1<<e
  fixtures.append({'source_F':source,'global_index':gid,'leaf_index':j,'graph':g})
start=time.monotonic();counts={};checks=[]
for fixture in fixtures:
 assert time.monotonic()-start<120
 g=fixture['graph'];fs,capacity=mods[0].families(g);out=json.loads(lib.check_projection((U*49)(*g),10000,time.monotonic()+5))
 empty=next((p for p,rows in fs.items() if not rows),None)
 if empty is not None:assert out['status']=='EMPTY_FAMILY' and out['pair_vertex']==empty
 else:
  expected=mods[1].solve(g,fs,capacity,time.monotonic()+5)
  assert expected['status']==out['status'],(fixture,out['status'],expected['status'])
  assert expected['nodes']==out['nodes']
  for k in ['order','tree']:assert expected[k]==out[k],k
  assert {str(p):rows for p,rows in fs.items()}==out['families'] and capacity==out['capacity']
  assert (None if expected['witness'] is None else {str(p):f for p,f in expected['witness'].items()})==out.get('witness')
 counts[out['status']]=counts.get(out['status'],0)+1;checks.append({'source_F':fixture['source_F'],'global_index':fixture['global_index'],'leaf_index':fixture['leaf_index'],'status':out['status'],'nodes':out['nodes']})
g=fixtures[0]['graph'];ga=(U*49)(*g);controls=[]
for label,graph,cap,deadline,expected in [('expired',ga,10000,time.monotonic()-1,'UNKNOWN'),('zero_nodes',ga,0,time.monotonic()+5,'UNKNOWN'),('negative_cap',ga,-1,time.monotonic()+5,'INVALID'),('nan_deadline',ga,10,float('nan'),'INVALID'),('null',None,10,time.monotonic()+5,'INVALID'),('zero_graph',(U*49)(),10,time.monotonic()+5,'INVALID')]:
 out=json.loads(lib.check_projection(graph,cap,deadline));assert out['status']==expected,(label,out);controls.append({'control':label,'status':out['status']})
(D/'fixtures.json').write_text(json.dumps(fixtures,separators=(',',':'))+'\n')
out={'status':'PASS_DIFFERENTIAL_QUALIFICATION','fixtures':len(fixtures),'counts':counts,'controls':controls,'checks':checks,'seconds':time.monotonic()-start,'source_pins':source_pins,'cpp_sha256':sha(D/'projection.cpp'),'dylib_sha256':sha(D/'projection.dylib'),'python_family_sha256':sha(A/'probe.py'),'python_choice_sha256':sha(B/'probe.py'),'scope':'Native API qualification only. F14 fixtures drawn only from accepted negative prefix; no remaining-domain exclusion.'}
(D/'qualification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['checks','source_pins']}))
