"""Exact controls for full-Gram parity redundancy; no q7 survivor is supplied."""
import json
from pathlib import Path
import sympy as s
z,t=s.symbols("z t")
def verify(name,A):
    n=A.rows
    assert A==A.T and all(A[i,i]==0 for i in range(n))
    p=s.Poly((s.eye(n)+z*A).det(),z)
    assert all(p.nth(k)%2==0 for k in range(1,n+1,2))
    E=sum(p.nth(k)*t**(k//2) for k in range(0,n+1,2))
    O=sum((p.nth(k)/2)*t**((k-1)//2) for k in range(1,n+1,2))
    q=s.expand((s.eye(n)+t*(A*A)).det())
    rhs=s.expand(E.subs(t,-t)**2+4*t*O.subs(t,-t)**2)
    assert s.expand(q-rhs)==0
    assert all(c%4==0 for c in s.Poly(q-E.subs(t,-t)**2,t).all_coeffs())
    # An independent integer recurrence checks the first12 root coefficients.
    coeff=[1]
    for k in range(1,13):
        v=s.Poly(q,t).nth(k)-sum(coeff[j]*coeff[k-j] for j in range(1,k))
        assert v%2==0
        coeff.append(v//2)
    return dict(name=name,order=n,det_I_plus_zA=str(p.as_expr()),
                det_I_plus_tA2=str(q),root_through_degree12=list(map(int,coeff)))
controls=[]
for n in (3,4,6): controls.append(("complete"+str(n),s.ones(n)-s.eye(n)))
P=s.zeros(5)
for i in range(4): P[i,i+1]=P[i+1,i]=1
controls.append(("path5",P))
W=s.zeros(5)
for i in range(5):
    for j in range(i+1,5): W[i,j]=W[j,i]=((i+2)*(j+3))%7-3
controls.append(("weighted_signed5",W))
rows=[verify(name,A) for name,A in controls]
# Omitting zero diagonal is invalid: A=[1] yields1+t, whose first root coefficient is1/2.
assert s.sqrt(1+t).series(t,0,2).removeO().coeff(t,1)==s.Rational(1,2)
result=dict(scope="Exact control matrices only, not a proof of the general lemma or a q7 completion",controls=rows,nonzero_diagonal_negative_control="A=[1], root t coefficient1/2")
Path(__file__).with_suffix(".json").write_text(json.dumps(result,indent=2)+"\n")
print("PASS:5 integer symmetric zero-diagonal controls; nonzero-diagonal negative control fails integrality as expected")
