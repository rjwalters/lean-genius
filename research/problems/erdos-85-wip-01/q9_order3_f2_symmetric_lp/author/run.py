from pathlib import Path
import json,time,itertools,math
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog
p=Path(__file__).parent;orbits=json.loads(Path('/tmp/erdos85-sol1-q9-order3-f2-symmetry/orbits.json').read_text());states=json.loads(Path('/tmp/erdos85-sol1-q9-order3-f2-contingency/receipts.json').read_text());start=time.monotonic();cap=60;receipts=[]
edges=list(itertools.combinations_with_replacement(range(20),2));index={e:i for i,e in enumerate(edges)};nv=2*len(edges)
def model(o):
 r=states[o['state']];T=r['tables'][o['table']];words=[(a,b) for a in range(3) for b in range(3) for _ in range(T[a][b])]
 if r['cross_orbits']==3:
  if r['missing_labels'] is None:words.append((3,3))
  else:i,j=r['missing_labels'];words.extend([(i,3),(3,j)])
 assert len(words)==20
 rows=[];rhs=[]
 def add(d,b):rows.append(d);rhs.append(b)
 for i,(a,b) in enumerate(words):
  ids=[index[tuple(sorted((i,j)))] for j in range(20)];degree=9-int(a<3)-int(b<3)
  add(dict.fromkeys(ids,1),degree);add(dict.fromkeys(ids,-1),-degree)
  for label in range(3):
   add({ids[j]:1 for j,w in enumerate(words) if w[0]==label},3-int(0<a<3 and label==3-a)-int(b<3 and r['mapping'][label]==b))
   add({ids[j]:1 for j,w in enumerate(words) if w[1]==label},3-int(0<b<3 and label==3-b)-int(a<3 and r['mapping'][a]==label))
  add({v+len(edges):1 for v in ids},1)
 for v in range(len(edges)):
  add({v:1},2);add({v:1,v+len(edges):-1},1)
 return rows,rhs

def scale(v):
 f=[(i,Fraction(float(x)).limit_denominator(1000000)) for i,x in enumerate(v) if abs(x)>1e-9]
 den=math.lcm(*(x.denominator for i,x in f));return den,[(i,int(x*den)) for i,x in f]
for oi,o in enumerate(orbits):
 left=cap-(time.monotonic()-start)
 if left<=0:break
 rows,rhs=model(o);A=np.zeros((len(rows),nv+1))
 for i,row in enumerate(rows):
  for j,v in row.items():A[i,j]=v
 A[:,-1]=-1;cost=np.zeros(nv+1);cost[-1]=1
 sol=linprog(cost,A_ub=A,b_ub=rhs,bounds=(0,None),method='highs',options={'time_limit':max(.001,cap-(time.monotonic()-start))})
 rec={'orbit':oi,'state':o['state'],'table':o['table'],'size':o['size'],'solver_status':int(sol.status),'status':'UNKNOWN'}
 if sol.status==0:
  # Save numerical discovery before exact reconstruction.
  candidate={'x':sol.x.tolist(),'dual':sol.ineqlin.marginals.tolist(),'objective':float(sol.fun)}
  (p/f'candidate-{oi}.json').write_text(json.dumps(candidate)+'\n')
  if sol.fun<1e-7:
   den,w=scale(sol.x[:-1]);values=dict(w)
   if all(v>=0 for _,v in w) and all(sum(v*values.get(j,0) for j,v in row.items())<=den*b for row,b in zip(rows,rhs)):
    rec.update(status='EXACT_FEASIBLE',denominator=den,witness=w)
  else:
   den,w=scale(-sol.ineqlin.marginals);coeff=[0]*nv;dot=0
   for i,v in w:
    dot+=v*rhs[i]
    for j,a in rows[i].items():coeff[j]+=v*a
   if all(v>=0 for _,v in w) and min(coeff)>=0 and dot<0:rec.update(status='EXACT_INFEASIBLE',certificate=w,rhs=dot)
 receipts.append(rec)
result={'original_wall_cap':cap,'seconds':time.monotonic()-start,'supplied':len(orbits),'visited':len(receipts),'unvisited':len(orbits)-len(receipts),'counts':{s:sum(r['status']==s for r in receipts) for s in ['EXACT_FEASIBLE','EXACT_INFEASIBLE','UNKNOWN']}}
(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');(p/'receipts.json').write_text(json.dumps(receipts)+'\n');print(json.dumps(result))
