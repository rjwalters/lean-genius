"""Fixed q16 examples of the uniform reflection determinant factorization."""
from pathlib import Path
from math import gcd,isqrt
import sympy as sp
import json
ROOT=Path(__file__).parent

def check(q,reps):
 n=q*q;h=n//2;r=sum(a%2 for a in reps)
 assert len(reps)==(q-2)//2 and len(set(reps))==len(reps)
 assert all(0<a<h for a in reps)
 assert gcd(n,*reps)==1 and r>0
 steps={h}|{a%n for v in reps for a in [v,-v]}
 D=sp.zeros(n)
 for i in range(n):
  for s in steps:D[i,(i+s)%n]=1
 M=(q-1)*sp.eye(n)+sp.ones(n)-D
 minus=sp.zeros(n,h-1);plus=sp.zeros(n,h+1)
 plus[0,0]=1;plus[h,1]=1
 for j in range(1,h):
  minus[j,j-1]=1;minus[n-j,j-1]=-1
  plus[j,j+1]=1;plus[n-j,j+1]=1
 B=(M*minus).extract(list(range(1,h)),list(range(h-1)))
 C=(M*plus).extract([0,h]+list(range(1,h)),list(range(h+1)))
 assert M*minus==minus*B and M*plus==plus*C
 shift=sp.zeros(n)
 for i in range(n):shift[(i+1)%n,i]=1
 T=shift-shift.T
 L=(T*plus).extract(list(range(1,h)),list(range(h+1)))
 assert T*plus==minus*L and L*C==B*L
 assert L.rank()==h-1
 one=sp.ones(n,1);alt=sp.Matrix([(-1)**i for i in range(n)])
 assert M*one==n*one and M*alt==4*r*alt
 assert T*one==T*alt==sp.zeros(n,1)
 P=B.det(method='domain-ge');detplus=C.det(method='domain-ge')
 assert P!=0 and detplus==n*4*r*P
 detM=detplus*P
 assert detM==4*q*q*r*P*P
 # Direct F2 polynomial valuation; this is only the existing valuation-two test.
 mask=[int(M[0,j])%2 for j in range(n)]
 valuation=next(j for j in range(n) if sum(mask[a] for a in range(n) if a&j==j)%2)
 out={'q':q,'n':n,'representatives':reps,'odd_count':r,'minus_determinant':str(P),'plus_determinant':str(detplus),'full_determinant_from_blocks':str(detM),'factorization':'4*q²*r*P²','intertwiner_rank':h-1,'mod2_valuation':valuation,'square_determinant':isqrt(detM)**2==detM,'old_nullity_two_obstruction':valuation==2,'PASS':True}
 print(q,reps,'r',r,'valuation',valuation,'det square',out['square_determinant'],'PASS',flush=True)
 return out

if __name__=='__main__':
 results=[check(16,[1,2,4,6,8,10,12]),check(16,list(range(1,8)))]
 (ROOT/'verification.json').write_text(json.dumps(results,indent=2)+'\n')
