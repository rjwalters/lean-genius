"""Two exact monic integer polynomial controls; no graph or full search claim."""
import json
import math
from pathlib import Path
import sympy as s

x,a=s.symbols('x a')
CONTROLS={
 5: {'T':19,'R':16,'factors':[([1,-3],2),([1,3],2),([1,0,-6],8),([1,0,-3],2),([1,1,-7],4),([1,1,-4],2),([1,1,-3],1)]},
 7: {'T':13,'R':30,'factors':[([1,-1,-5],1),([1,0,-7],5),([1,0,-6],2),([1,0,-3],1),([1,1,-7],3),([1,1,-5],3),([1,1,-3],2)]}
}

def mul(a,b,limit=None):
 n=len(a)+len(b)-1
 if limit is not None:n=min(n,limit+1)
 out=[0]*n
 for i,v in enumerate(a):
  for j,w in enumerate(b):
   if i+j<n:out[i+j]+=v*w
 return out

profiles=json.loads(Path(__file__).with_name('verify_q7_local_defect_overlap_bound.json').read_text())['profiles']
results=[]
for h,control in CONTROLS.items():
 T,R=control['T'],control['R'];P=s.Poly(1,x);blocks=[]
 lo=(7-s.sqrt(49-4*h))/2;hi=(17+s.sqrt(49-4*h))/2
 H=[1,-7,12,-42-h,78+h,-294,252];bass=H[:]
 for coefficients,multiplicity in control['factors']:
  factor=s.Poly.from_list(coefficients,x);P*=factor**multiplicity
  roots=s.solve(factor.as_expr(),x)
  assert all(bool(z*z>lo) and bool(z*z<hi) for z in roots)
  c=coefficients
  C=s.Matrix([[-c[1]]]) if len(c)==2 else s.Matrix([[0,-c[2]],[1,-c[1]]])
  blocks.append((C,6*s.eye(C.rows)-C*C,multiplicity))
  local=[1,c[1],6] if len(c)==2 else [1,c[1],12+c[2],6*c[1],36]
  for _ in range(multiplicity):bass=mul(bass,local)
 powers=[int(sum(m*s.trace(C**j) for C,D,m in blocks)) for j in range(7)]
 assert powers[:6]==[48-2*h,-7,294-13*h,21*h-343+6*T,2058-97*h,R+72*T+269*h-4116]
 assert P.degree()==48-2*h and P.LC()==1
 mod,root=(13,8) if h==5 else (5,3)
 assert P.eval(root)%mod==0
 assert P.eval(0)!=0 and P.eval(0)%(7**(h-1))==0
 assert all(P.nth(j)%7==0 for j in range(h-1))
 reduced=mul(bass,[1,0,-1]) if h==5 else bass[:]
 binary=[reduced[2*j]%2 for j in range((len(reduced)+1)//2)]
 square=mul(binary,binary)
 assert all((v-(square[j] if j<len(square) else 0))%4==0 for j,v in enumerate(reduced))
 Q,rem=s.div(P,s.Poly(x*x+x+1,x),domain=s.GF(2));assert rem.is_zero
 assert all(Q.nth(j)%2==0 for j in range(1,Q.degree()+1,2))
 S=sum((int(Q.nth(2*j))%2)*x**j for j in range(Q.degree()//2+1))
 if h==5:
  error=s.rem(P.as_expr().subs(x,a)-4*(7-a)*S.subs(x,7-a),a*a-7*a+5,a)
  assert all(int(c)%8==0 for c in s.Poly(error,a).all_coeffs())
 upper={p['profile']:next(r['R_upper_bound'] for r in p['triangle_rows'] if r['T']==T) for p in profiles if p['h']==h}
 assert all(0<=R<=v for v in upper.values()) and R%2==0 and (R-3*T-h-4)%5==0
 quotient=s.Matrix([[7,h],[-1,0]])
 blocks.extend([(quotient,quotient-s.eye(2),1),(s.zeros(1),s.Matrix([[-1]]),h-1)])
 mixed=[[int(sum(m*s.trace(C**i*D**j) for C,D,m in blocks)) for j in range(9)] for i in range(9)]
 assert all(v>=0 for row in mixed for v in row)
 assert mixed[0][3]==15876-790*h-powers[6] and mixed[0][3]%6==0
 assert mixed[1][2]==R
 # Full A Bass polynomial, using the actual mixed-degree factors.
 limit=20;full=bass[:limit+1]
 for _ in range(h-1):full=mul(full,[1,0,6,0,42],limit)
 for _ in range((245+h)//2):full=mul(full,[1,0,-1],limit)
 traces=[0]*(limit+1);cycles=[0]*(limit+1)
 for j in range(1,limit+1):
  traces[j]=-j*full[j]-sum(full[i]*traces[j-i] for i in range(1,j))
  numerator=traces[j]-sum(i*cycles[i] for i in range(1,j) if j%i==0)
  assert numerator%j==0;cycles[j]=numerator//j
  assert cycles[j]>=0 and cycles[j]%2==0
 assert cycles[1:5]==[0,0,2*(4*h+T),0]
 results.append(dict(h=h,T=T,R=R,factors=control['factors'],coefficients_descending=list(map(int,P.all_coeffs())),
   residual_power_sums_0_to6=powers,local_R_upper_bounds=upper,defect_triangle_count=mixed[0][3]//6,
   mixed_trace_table_i_j_0_to8=mixed,full_A_primitive_oriented_counts_through20=cycles[1:]))
out={'scope':'Two fixed monic integer polynomial controls only; no simultaneous integral symmetric C/D, kernel-lattice representation, off-diagonal projectors, or graph witness','controls':results}
Path(__file__).with_name('q7_h5_h7_integer_spectral_controls.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: both integer polynomials satisfy the listed exact scalar gates; no graph or simultaneous matrix construction')
