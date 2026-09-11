from pathlib import Path
from collections import Counter
import json,hashlib,importlib.util,time
src=Path('/tmp/erdos85-sol1-q9-order3-f2-model-generator');out=Path(__file__).parent;start=time.monotonic();cap=60
read=lambda p:json.loads(p.read_text())
pins=read(src/'pins.json')
for f,h in pins.items():assert hashlib.sha256((src/f).read_bytes()).hexdigest()==h,f
inputs=read(src/'input-pins.json')
for f,h in inputs.items():assert hashlib.sha256(Path(f).read_bytes()).hexdigest()==h,f
orbits=read(Path('/tmp/erdos85-sol1-q9-order3-f2-symmetry/orbits.json'));states=read(Path('/tmp/erdos85-sol1-q9-order3-f2-contingency/receipts.json'));manifest=read(src/'model-manifest.json');assert len(orbits)==len(manifest)==117
spec=importlib.util.spec_from_file_location('submitted_generator',src/'generate.py');producer=importlib.util.module_from_spec(spec);spec.loader.exec_module(producer)
pairs=[(i,j) for i in range(20) for j in range(i,20)];B=[[0]*20 for _ in range(20)]
for index,(i,j) in enumerate(pairs):B[i][j]=B[j][i]=index
verified=[];constraints_checked=0
for oi,o in enumerate(orbits):
 if time.monotonic()-start>cap:break
 s=states[o['state']];table=s['tables'][o['table']];words=[]
 for a in range(3):
  for b in range(3):words.extend([(a,b)]*table[a][b])
 if s['cross_orbits']==3:
  if s['missing_labels'] is None:words.append((3,3))
  else:words.extend([(s['missing_labels'][0],3),(3,s['missing_labels'][1])])
 assert len(words)==20
 attached=[set() for _ in range(6)]
 for a,b in [(1,2),(4,5)]+[(i,j+3) for i,j in enumerate(s['mapping']) if j>=0]:attached[a].add(b);attached[b].add(a)
 expected={}
 def add(key,terms,lo=None,hi=None):
  c=Counter()
  for v,x in terms:c[v]+=x
  expected[tuple(key)]=(tuple(sorted((v,x) for v,x in c.items() if x)),lo,hi)
 def qterms(i,j):return [(B[i][j],1),(B[i][j]+210,1)]
 for i,j in pairs:add(('double_implies_present',i,j),[(B[i][j]+210,1),(B[i][j],-1)],hi=0)
 for i,w in enumerate(words):
  add(('diagonal',i),[(B[i][i],1),(B[i][i]+210,-1)],0,0)
  add(('one_double',i),[(B[i][j]+210,1) for j in range(20)],hi=1)
  present={side*3+value for side,value in enumerate(w) if value<3};degree=9-len(present)
  add(('degree',i),[t for j in range(20) for t in qterms(i,j)],degree,degree)
  for endpoint in range(6):
   side,value=divmod(endpoint,3);capacity=3-len(attached[endpoint]&present)
   add(('attached_margin',i,side,value),[t for j,z in enumerate(words) if z[side]==value for t in qterms(i,j)],hi=capacity)
 for pair_index,(i,j) in enumerate((i,j) for i in range(20) for j in range(i+1,20)):
  auxiliaries=[]
  for k in range(20):
   for term,(left_double,right_double) in enumerate([(0,0),(1,0),(0,1)]):
    z=420+60*pair_index+3*k+term;left=B[i][k]+210*left_double;right=B[j][k]+210*right_double
    assert left!=right
    add(('product_lower',i,j,k,term),[(left,1),(right,1),(z,-1)],hi=1);auxiliaries.append((z,1))
  common=len({(side,value) for side,value in enumerate(words[i]) if value<3}&{(side,value) for side,value in enumerate(words[j]) if value<3})
  add(('two_step',i,j),auxiliaries,hi=3-common)
 model=producer.build(oi)
 assert model['schema']=='erdos85-f2-integral-quotient-v1' and model['objective'] is None
 assert model['variables']=={'count':11820,'binary_range':[0,420],'nonnegative_continuous_range':[420,11820]}
 assert model['representative']==oi and model['source_state']==o['state'] and model['source_table']==o['table'] and model['orbit_size']==o['size']
 assert model['words']==words and model['matrix_pair_order']==pairs and model['cross_mapping']==s['mapping']
 actual={tuple(r['name']):(tuple(tuple(t) for t in r['terms']),r['lower'],r['upper']) for r in model['constraints']}
 assert len(actual)==len(model['constraints'])==len(expected)==11980 and actual==expected
 raw=json.dumps(model,separators=(',',':'),sort_keys=True).encode()+b'\n';digest=hashlib.sha256(raw).hexdigest();entry=manifest[oi]
 assert entry=={'representative':oi,'sha256':digest,'bytes':len(raw),'variables':11820,'constraints':11980}
 if oi==0:assert raw==(src/'model-0.json').read_bytes()
 verified.append(oi);constraints_checked+=len(expected)
result={'status':'COMPLETE_PASS' if len(verified)==117 else 'UNKNOWN','original_review_cap_seconds':cap,'seconds':time.monotonic()-start,'models':len(verified),'unvisited':117-len(verified),'constraints_checked':constraints_checked,'source_pins':len(pins),'input_pins':len(inputs),'optimizer_calls':0}
(out/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result));assert result['status']=='COMPLETE_PASS'
(out/'input-pins.json').write_text(json.dumps({str(src/'pins.json'):hashlib.sha256((src/'pins.json').read_bytes()).hexdigest(),**inputs},indent=2)+'\n')
