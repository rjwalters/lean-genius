from pathlib import Path
from fractions import Fraction as F
import json,itertools as it,time,hashlib,collections,ast
b=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3');p=b/'residual-ten-D5-five-311-common-neighbor-cuts';o=Path(__file__).parent
def read(f):return json.loads(f.read_text())
# Reuse only the already reviewed sparse rational-certificate routine; no earlier audit runs.
tree=ast.parse((o.parent/'review-2486/audit.py').read_text());node=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='certificates');exec(compile(ast.Module(body=[node],type_ignores=[]),'<certificate-function>','exec'))
nh=0
for fn in ['pins.json','input-pins.json']:
 for k,v in read(p/fn).items():
  q=Path(k);q=q if q.is_absolute() else p/q
  assert hashlib.sha256(q.read_bytes()).hexdigest()==v;nh+=1
old=read(b/'residual-ten-D5-five-311-low-edge-allocation/models.json')['records'];oldresults={r['root']:r for r in read(b/'residual-ten-D5-five-311-low-edge-allocation/results.json')['records']};prior={r['root']:r for r in old if oldresults[r['root']]['status']!='EXACT_FARKAS_CONTRADICTION'}
data=read(p/'models.json');result=read(p/'results.json');models={r['root']:r for r in data['records']};assert data['status']=='COMPLETE' and result['status']=='INCOMPLETE' and len(models)==len(data['records'])==len(prior)==91 and models.keys()==prior.keys()
prop={r['root']:r for r in read(b/'residual-ten-D5-five-311-low-propagation/results.json')['records']};edges={r['root']:r for r in read(b/'residual-ten-D5-five-311-low-edge-capacity/results.json')['records']};joint={r['root']:r for r in read(b/'residual-ten-D5-five-311-nonempty-joint/results.json')['records']};graphs={r['root']:r for r in read(b/'residual-ten-D5-five-311-high-matchings/results.json')['records']};pack=read(b/'residual-ten-D5-five-311-packing/results.json')['records'];dom=read(b/'residual-ten-D5-supports/results.json')['records'];start=time.monotonic();status='INCOMPLETE';ncuts=0
def guard():
 if time.monotonic()-start>30:raise TimeoutError
try:
 for key,m in models.items():
  guard();base=prior[key]
  for field in ['root','source_root','assignment','class','variables','bounds']:assert m[field]==base[field]
  nbase=len(base['constraints']);assert m['constraints'][:nbase]==base['constraints'] and len(m['constraints'])==nbase+len(m['new_cuts'])
  src=m['source_root'];ai=m['assignment'];source=joint[src];ci=source['class'];d=dom[ci];root=pack[ci]['survivors'][source['source_root']];S=[]
  for j in root['high3']:
   s=set(d['high3'][j]);S.extend([s,{v^1 for v in s}])
  lows=next(x['lows'] for x in edges[src]['survivors'] if x['assignment']==ai);a=next(x for x in prop[src]['survivors'] if x['assignment']==ai);N=[set() for _ in range(70)];V=[{} for _ in range(70)]
  def edge(v,w):N[v].add(w);N[w].add(v)
  for v,w in d['edges']:edge(v,w)
  for v,s in enumerate(S):
   for r in s:edge(10+v,r)
  for v,w in graphs[source['packing_root']]['survivors'][source['graph']]['edges']:edge(10+v,10+w)
  for i,(v,r) in enumerate(lows):
   edge(20+i,r)
   if v>=0:edge(20+i,10+v)
  for i,j in a['forced_edges']:edge(20+i,20+j)
  for k,var in enumerate(m['variables']):
   i,j=var['edge'];V[20+i][20+j]=k;V[20+j][20+i]=k
  seen=set()
  for witness,con in zip(m['new_cuts'],m['constraints'][nbase:]):
   i,j=witness['pair'];assert 0<=i<j<70 and (i,j) not in seen;seen.add((i,j))
   fixed=len(N[i]&N[j]);assert fixed<=1 and fixed==witness['fixed_common']
   linear=[V[j][z] for z in N[i]&V[j].keys()]+[V[i][z] for z in N[j]&V[i].keys()];assert collections.Counter(linear)==collections.Counter(witness['linear_paths'])
   coeff=collections.Counter(linear);selected=witness['selected_paths'];middles=set()
   for z,v,w in selected:
    assert z not in middles and V[i].get(z)==v and V[j].get(z)==w;middles.add(z);coeff[v]+=1;coeff[w]+=1
   upper=1-fixed+len(selected);assert upper==witness['upper']==con['upper'] and con['lower']==0 and con['coefficients']==[list(x) for x in sorted(coeff.items())]
  ncuts+=len(m['new_cuts'])
 assert ncuts==121859
 outcomes=certificates(models,result,guard);assert outcomes=={'EXACT_FARKAS_CONTRADICTION':47,'EXACT_RATIONAL_WITNESS':24,'UNKNOWN':20};status='COMPLETE'
except TimeoutError:outcomes=None
receipt={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'hashes':nh,'cuts':ncuts,'outcomes':outcomes};(o/'audit.json').write_text(json.dumps(receipt,indent=2)+'\n');print(receipt)
