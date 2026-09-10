"""Exact necessary identities only; this does not construct or exclude A."""
import json
from itertools import combinations
from pathlib import Path
import sympy as s
x=s.symbols("x")
results=[]
for h in (1,3):
    f=x**3-7*x**2-7*x+49-h
    Q=s.Matrix([[7,0,h],[1,0,7],[0,1,0]])
    assert s.expand(Q.charpoly(x).as_expr()-f)==0
    assert s.Poly(f,x).is_irreducible
    G=s.Matrix([[49,h,8*h],[h,h,0],[8*h,0,h*(h+7)]])
    assert G.det()==h*h*(343-22*h-h*h)
    moments=[-(s.trace(Q)),343+h-s.trace(Q**2)-14*(h-1),
             4459+29*h-s.trace(Q**4)-98*(h-1)]
    assert moments==[-7,294-13*h,2058-97*h]
    assert 24*h-s.trace(Q**3)==21*h-343
    Cq=s.Matrix([[7,h],[-1,0]])
    Dq=s.Matrix([[6,h],[-1,-1]])
    assert Cq.charpoly(x).as_expr()==x*x-7*x+h
    assert Dq.charpoly(x).as_expr()==x*x-5*x+h-6
    support_rows=[]
    for triple in ((0,) if h==1 else (0,1)):
        supports=[]
        if h==1:
            supports=[(0,)]*8+[()]*40
        else:
            supports += [tuple(range(3))]*triple
            for pair in combinations(range(3),2): supports += [pair]*(1-triple)
            for i in range(3): supports += [(i,)]*(6+triple)
            supports += [()]*(25-triple)
        B=s.Matrix([[int(i in z) for z in supports] for i in range(h)])
        assert B.shape==(h,49-h)
        assert B*B.T==7*s.eye(h)+s.ones(h,h)
        assert B*s.ones(49-h,1)==8*s.ones(h,1)
        U=B.col_join(s.ones(1,49-h))
        gram=U*U.T
        expected=7**(h-1)*(343-22*h-h*h)
        assert gram.det()==expected
        support_rows.append(dict(triple_count=triple,ambient_dimension=49-h,
            low_span_gram_determinant=int(gram.det()),
            support_size_counts={str(k):sum(len(z)==k for z in supports) for k in range(h+1)}))
    results.append(dict(h=h,cubic=str(f),residual_degree=48-2*h,
        residual_p1=int(moments[0]),residual_p2=int(moments[1]),
        residual_p3="6*T"+str(21*h-343),residual_p4=int(moments[2]),
        determinant_divisor=(49-h)*7**(h-1),support_profiles=support_rows))
output=dict(scope="Exact arithmetic and explicit incidence Gram witnesses only; no C completion and no exclusion",results=results)
Path(__file__).with_suffix(".json").write_text(json.dumps(output,indent=2)+"\n")
print(json.dumps(output,indent=2))
