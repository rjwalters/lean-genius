"""Exact algebra for universal H3 support-edge identities; no graph claim."""
import sympy as s
v=s.symbols('e00 e01 e02 e11 e12 e22');a,c,d,e,f,b=v
solution=s.solve([2*a+c+d-175,c+2*e+f-108,d+f+2*b-15,c+2*d-75,2*e+2*f-54,f+4*b-9],v,dict=True)
assert solution==[{a:b+53,c:63-4*b,d:2*b+6,e:4*b+18,f:9-4*b}]
for q in [0,1]:
    edges=[53+q,63-4*q,6+2*q,18+4*q,9-4*q,q]
    assert sum(edges)==149 and all(x>=0 for x in edges)
    # nP is binary. Its incidence totals over E,S,P determine nE=4-t+nP.
    nP=[6+2*q,9-4*q,2*q];sizes=[25,18,3]
    assert sum(nP)==15
    moment2=sum((size-n)*((4-t)**2)+n*((5-t)**2) for t,(size,n) in enumerate(zip(sizes,nP)))
    assert moment2==691
    assert (19-2*q)*4+(6+2*q)*5==2*(53+q)
    print('PASS pair b=',q,'edges=',edges,'empty degree counts4/5=',[19-2*q,6+2*q])
e00,e01,e03,e11,e13,e33=49,69,1,27,3,0
assert 2*e00+e01+e03==24*7
assert e01+2*e11+e13==21*6
assert e03+e13==4
assert e01+3*e03==24*3
assert 2*e11+3*e13==21*3
assert e13==3
assert e00+e01+e03+e11+e13==149
assert 23*4+6==2*e00
assert 23*4**2+6**2+18*3**2+3*5**2+1==642
print('PASS triple edges49/69/1/27/3/0; empty degree counts4/6=23/1; squared moment642')
print('Necessary support identities only; no profile exclusion or full graph realization.')
