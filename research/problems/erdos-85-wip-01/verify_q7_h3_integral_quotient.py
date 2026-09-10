"""Exact H3 quotient coefficients, not a graph existence/exclusion verifier."""
import itertools
import json
from pathlib import Path
import sympy as s

a, alpha, beta, gamma, delta = s.symbols('a alpha beta gamma delta')
f = a*a-7*a+3
red = lambda p: s.rem(s.expand(p), f, a)
cases = [
 ('12/22',72*a-30,130*a-48,[-12*beta+21*delta,-3*beta+5*delta],[[0,0,0,0]]),
 ('10/24',58*a-18,144*a-60,[2*beta-6*delta,s.Rational(7,2)*beta-9*delta],[[0,0,0,0]]),
 ('10/12',58*a-18,72*a-30,[2*beta-3*delta,7*beta-9*delta],[[0,0,0,0],[-1,1,-2,1]]),
]
rows=[]
for label,g,j,expected,allowed in cases:
 eqs=s.Poly(red(g*(alpha+beta*a)-j*(gamma+delta*a)),a).all_coeffs()
 solution=s.solve(eqs,(alpha,gamma))
 assert solution==dict(zip((alpha,gamma),expected))
 found=[]
 for b,d in itertools.product((0,1),repeat=2):
  for A in range(-7*b,8-7*b):
   for C in range(-7*d,8-7*d):
    if red(g*(A+b*a)-j*(C+d*a))==0:found.append([A,b,C,d])
 assert found==allowed
 rows.append(dict(component_pair=label,linear_solution={str(k):str(v) for k,v in solution.items()},allowed_cross_entries=found))
# For12/24, weighted symmetry gives m12,24=2*m24,12. The beta bound
# makes both beta coefficients zero; integral alpha gives2y,y with0<=y<=3.
remaining=[]
for b,d in itertools.product((0,1),repeat=2):
 for A in range(-7*b,8-7*b):
  for C in range(-7*d,8-7*d):
   if red((72*a-30)*(A+b*a)-(144*a-60)*(C+d*a))==0:
    remaining.append([A,b,C,d])
assert remaining==[[0,0,0,0],[2,0,1,0],[4,0,2,0],[6,0,3,0]]
x,y=s.symbols('x y')
M=s.Matrix([[x+(1-x)*a,x*(a-1),0],
            [x*(a-2),2*x-2*y+(1-x)*a,2*y],
            [0,y,a-y]])
assert M*s.ones(3,1)==a*s.ones(3,1) or all(s.expand(v)==0 for v in M*s.ones(3,1)-a*s.ones(3,1))
trace_candidates=[(X,Y) for X in (0,1) for Y in range(4)
                  if red(s.trace(M).subs({x:X,y:Y})-a)==0]
assert trace_candidates==[(1,1)]
forced_det=red(M.subs({x:1,y:1}).det())
assert forced_det==9-23*a
assert red(a*(7-a))==3
assert red(forced_det+3)==12-23*a
assert 1+6*5>24
out=dict(scope='Exact scalar systems and quotient trace/determinant only; graph reduction remains paper',sympy_version=s.__version__,cross_entry_checks=rows,
         remaining_12_24_cross_entries=remaining,trace_candidates=trace_candidates,
         forced_determinant=str(forced_det),required_determinant=-3,
         contradiction='Equality would force a=12/23, incompatible with a>6')
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
