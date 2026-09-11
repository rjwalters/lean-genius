from pathlib import Path
from fractions import Fraction as F
import json,itertools as it,time,hashlib,collections
b=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3');o=Path(__file__).parent
def read(f):return json.loads(f.read_text())
names=['residual-ten-D5-five-311-low-involution','residual-ten-D5-five-311-low-orbit-capacity'];nh=0
for name in names:
 p=b/name
 for fn in ['pins.json','input-pins.json']:
  for k,v in read(p/fn).items():
   q=Path(k);q=q if q.is_absolute() else p/q
   assert hashlib.sha256(q.read_bytes()).hexdigest()==v;nh+=1
old=read(b/'residual-ten-D5-five-311-common-neighbor-cuts/models.json')['records'];oldresults={r['root']:r for r in read(b/'residual-ten-D5-five-311-common-neighbor-cuts/results.json')['records']};prior={r['root']:r for r in old if oldresults[r['root']]['status']!='EXACT_FARKAS_CONTRADICTION'}
prop={r['root']:r for r in read(b/'residual-ten-D5-five-311-low-propagation/results.json')['records']};edgecases={r['root']:r for r in read(b/'residual-ten-D5-five-311-low-edge-capacity/results.json')['records']}
def canonical(c):return (tuple(sorted(tuple(x) for x in c['coefficients'])),c['lower'],c['upper'])
def constraint(co,l,u):return {'coefficients':co,'lower':l,'upper':u}
def certificates(models,result,guard):
 by={r['root']:r for r in result['records']};assert len(by)==len(result['records'])==len(models) and by.keys()==models.keys();counts=collections.Counter()
 for key,m in models.items():
  guard();r=by[key];assert r['source_root']==m['source_root'] and r['source_assignment']==m['assignment'] and r['class']==m['class'];counts[r['status']]+=1
  if r['status']=='UNKNOWN':continue
  if r['status']=='EXACT_RATIONAL_WITNESS':
   x=list(map(F,r['assignment']));assert len(x)==len(m['variables'])
   assert all(l<=v<=u for v,(l,u) in zip(x,m['bounds']))
   for c in m['constraints']:
    value=sum(a*x[j] for j,a in c['coefficients']);assert c['lower']<=value<=c['upper']
  else:
   assert r['status']=='EXACT_FARKAS_CONTRADICTION';coeff=[F(0)]*len(m['variables']);rhs=F(0)
   for term in r['terms']:
    label=term['label'];weight=F(term['weight']);assert weight>=0;kind,j,side=label;sign=1 if side=='upper' else -1;assert side in ['upper','lower']
    if kind=='constraint':
     c=m['constraints'][j];co=c['coefficients'];bound=c[side]
    else:assert kind=='bound';co=[[j,1]];bound=m['bounds'][j][1 if side=='upper' else 0]
    rhs+=weight*sign*bound
    for h,a in co:coeff[h]+=weight*sign*a
   assert not any(coeff) and rhs==F(r['rhs']) and rhs<0
 return dict(counts)
stages=[]
for stage,name in enumerate(names):
 data=read(b/name/'models.json');result=read(b/name/'results.json');assert data['status']=='COMPLETE';models={r['root']:r for r in data['records']};assert len(models)==len(data['records'])==len(prior)==44 and models.keys()==prior.keys();start=time.monotonic();status='INCOMPLETE';added=0
 def guard():
  if time.monotonic()-start>30:raise TimeoutError
 try:
  for key,m in models.items():
   guard();base=prior[key]
   for field in ['variables','bounds','root','source_root','class','assignment']:assert m[field]==base[field]
   assert m['constraints'][:len(base['constraints'])]==base['constraints']
   source=m['source_root'];ai=m['assignment'];a=next(x for x in prop[source]['survivors'] if x['assignment']==ai);forced={tuple(e) for e in a['forced_edges']};lookup={tuple(v['edge']):j for j,v in enumerate(m['variables'])};expected=[]
   if stage==0:
    lows=next(x['lows'] for x in edgecases[source]['survivors'] if x['assignment']==ai);active={tuple(x):i for i,x in enumerate(lows) if x[0]>=0};inactive={r:[i for i,(v,s) in enumerate(lows) if v<0 and s==r] for r in range(10)};tau=[]
    for i,(v,r) in enumerate(lows):tau.append(active[v^1,r^1] if v>=0 else inactive[r^1][inactive[r].index(i)])
    assert all(tau[tau[i]]==i and tau[i]!=i for i in range(50)) and tau==m['low_tau']
    for e,j in lookup.items():
     image=tuple(sorted(tau[v] for v in e))
     if image in lookup:
      h=lookup[image]
      if j<h:expected.append(constraint([[j,1],[h,-1]],0,0))
     else:
      value=int(image in forced);expected.append(constraint([[j,1]],value,value))
    for e in forced:
     image=tuple(sorted(tau[v] for v in e))
     if image in lookup:expected.append(constraint([[lookup[image],1]],1,1))
     elif image not in forced:expected.append(constraint([],1,1))
    assert collections.Counter(map(canonical,expected))==collections.Counter(map(canonical,m['tau_constraints']))
   else:
    tau=base['low_tau'];assert m['low_tau']==tau
    for i,j in it.combinations([i for i in range(50) if i<tau[i]],2):
     edges=[tuple(sorted((i,j))),tuple(sorted((i,tau[j])))];constant=sum(e in forced for e in edges);co=[[lookup[e],1] for e in edges if e in lookup]
     if co or constant>1:expected.append(constraint(co,-constant,1-constant))
    assert collections.Counter(map(canonical,expected))==collections.Counter(map(canonical,m['orbit_capacity_cuts']))
   added+=len(expected);assert collections.Counter(map(canonical,expected))==collections.Counter(map(canonical,m['constraints'][len(base['constraints']):]))
  outcomes=certificates(models,result,guard)
  if stage==0:assert added==11227 and result['status']=='INCOMPLETE' and outcomes=={'EXACT_RATIONAL_WITNESS':43,'UNKNOWN':1} and next(r['root'] for r in result['records'] if r['status']=='UNKNOWN')==6
  else:assert added==9480 and result['status']=='COMPLETE' and outcomes=={'EXACT_FARKAS_CONTRADICTION':3,'EXACT_RATIONAL_WITNESS':41}
  status='COMPLETE'
 except TimeoutError:outcomes=None
 receipt={'stage':stage,'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'added_constraints':added,'outcomes':outcomes};stages.append(receipt);(o/f'stage{stage}.json').write_text(json.dumps(receipt,indent=2)+'\n');print(receipt,flush=True)
 if status!='COMPLETE':break
 prior=models
(o/'audit.json').write_text(json.dumps({'hashes':nh,'stages':stages},indent=2)+'\n')
