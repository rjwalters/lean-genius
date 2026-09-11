from pathlib import Path
import itertools,json,time,math
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog
p=Path(__file__).resolve().parent
orbits=[json.loads(x) for x in (p.parent/'q9-order3-permutation-symmetry/orbits.jsonl').read_text().splitlines()]
words=list(itertools.product(range(3),repeat=5));ps=list(itertools.permutations(range(3)));pairs=list(itertools.combinations(range(5),2));labels=[];rows=[]
for u in range(5):
 for a in range(3):
  for s in [-1,1]:labels.append(['margin',u,a,s]);rows.append([s*int(w[u]==a) for w in words])
for u,v in pairs:
 for a in range(3):
  for b in range(3):labels.append(['pair',u,v,a,b]);rows.append([int(w[u]==a and w[v]==b) for w in words])
Aall=np.array(rows,dtype=np.int64)
start=time.monotonic();counts={};out=(p/'receipts.jsonl').open('w')
def integers(xs):
 f=[Fraction(float(x)).limit_denominator(1000000) for x in xs];den=math.lcm(*(x.denominator for x in f));return [int(x*den) for x in f]
for o in orbits:
 code=o['representative_code'];r={'code':code,'orbit_size':o['orbit_size']}
 if time.monotonic()-start>=60:r['status']='UNVISITED'
 else:
  z=code;ds=[0]*10
  for i in range(9,-1,-1):ds[i]=z%6;z//=6
  P={}
  for (u,v),z in zip(pairs,ds):P[u,v]=ps[z];P[v,u]=tuple(ps[z].index(a) for a in range(3))
  bounds={}
  for u,v in pairs:
   for a in range(3):
    for b in range(3):bounds[u,v,a,b]=3-int(a!=0 and P[u,v][3-a]==b)-int(P[u,v][a]!=0 and 3-P[u,v][a]==b)-sum(P[t,v][P[u,t][a]]==b for t in range(5) if t not in (u,v))
  ids=[i for i,w in enumerate(words) if all(bounds[u,v,w[u],w[v]]>0 for u,v in pairs)]
  A=Aall[:,ids];rhs=np.array([lab[3]*(4,3,3)[lab[2]] if lab[0]=='margin' else bounds[tuple(lab[1:])] for lab in labels],dtype=np.int64)
  remaining=max(.001,60-(time.monotonic()-start))
  sol=linprog(np.zeros(120),A_ub=-A.T,b_ub=np.zeros(len(ids)),A_eq=[rhs],b_eq=[-1],bounds=(0,None),method='highs',options={'time_limit':remaining})
  r['dual_status']=int(sol.status);r['supported_words']=len(ids)
  if sol.success:
   y=integers(sol.x);active=[(i,v) for i,v in enumerate(y) if v]
   ok=all(v>=0 for v in y) and all(sum(v*int(A[i,j]) for i,v in active)>=0 for j in range(len(ids))) and sum(v*int(rhs[i]) for i,v in active)<0
   r['status']='EXACT_INFEASIBLE' if ok else 'UNKNOWN_RATIONALIZATION'
   if ok:r['certificate']=active
  elif sol.status==2 and time.monotonic()-start<60:
   sol=linprog(np.zeros(len(ids)),A_ub=A,b_ub=rhs,bounds=(0,None),method='highs',options={'time_limit':max(.001,60-(time.monotonic()-start))})
   if sol.success:
    f=[Fraction(float(x)).limit_denominator(1000000) for x in sol.x];den=math.lcm(*(x.denominator for x in f));x=[int(v*den) for v in f];active=[(j,v) for j,v in enumerate(x) if v]
    ok=all(v>=0 for v in x) and all(sum(v*int(A[i,j]) for j,v in active)<=int(rhs[i])*den for i in range(120))
    r['status']='EXACT_FRACTIONAL_FEASIBLE' if ok else 'UNKNOWN_RATIONALIZATION'
    if ok:r['denominator']=den;r['witness']=[(ids[j],v) for j,v in active]
   else:r['status']='UNKNOWN_PRIMAL'
  else:r['status']='UNKNOWN_DUAL'
 counts[r['status']]=counts.get(r['status'],0)+1;out.write(json.dumps(r)+'\n');out.flush()
out.close();summary={'original_wall_cap_seconds':60,'seconds':time.monotonic()-start,'cases':len(orbits),'counts':counts};(p/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
