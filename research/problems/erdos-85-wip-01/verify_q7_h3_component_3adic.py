"""Exact arithmetic certificate for the conditional H3 12+12+22 obstruction."""
import json
from itertools import product
from pathlib import Path
import sympy as s
a=s.symbols("a")
f=a*a-7*a+3
red=lambda p:s.rem(s.expand(p),f,a)
g=red(12*a*a-12*a+6)
h=red(22*a*a-24*a+18)
G=red(2*g+h)
assert g==72*a-30 and h==130*a-48 and G==274*a-108
gram=s.diag(g,g,h)
v1=s.Matrix([1,-1,0]);v2=s.Matrix([h,h,-2*g]);one=s.ones(3,1)
assert red((v1.T*gram*one)[0])==0
assert red((v2.T*gram*one)[0])==0
assert red((v1.T*gram*v2)[0])==0
assert red((v1.T*gram*v1)[0]-2*g)==0
assert red((v2.T*gram*v2)[0]-2*g*h*G)==0
delta=red(h*G)
b=7-a
assert red(b*a)==3
assert f.subs(a,4)%9==0 and s.diff(f,a).subs(a,4)%3!=0
b9=int(b.subs(a,4)%9);d9=int(delta.subs(a,4)%9)
assert (b9,d9)==(3,1)
primitive=[]
for u,v,z in product(range(9),repeat=3):
    if (u*u+d9*v*v-b9*z*z)%9==0 and any(x%3 for x in (u,v,z)):
        primitive.append([u,v,z])
assert primitive==[]
g10=red(10*a*a-12*a+12)
assert g10==58*a-18 and red(g10+3*g-G)==0
gram2=s.diag(g10,g,2*g)
w1=s.Matrix([0,2,-1]);w2=s.Matrix([6*g,-2*g10,-2*g10])
assert red((w1.T*gram2*one)[0])==0
assert red((w2.T*gram2*one)[0])==0
assert red((w1.T*gram2*w2)[0])==0
assert red((w1.T*gram2*w1)[0]-6*g)==0
delta2=red(2*g10*G)
assert red((w2.T*gram2*w2)[0]-6*g*delta2)==0
assert f.subs(a,16)%49==0 and s.diff(f,a).subs(a,16)%7!=0
b49=int(b.subs(a,16)%49);d49=int(delta2.subs(a,16)%49)
assert (b49,d49)==(40,42)
primitive49=[]
for u,v,z in product(range(49),repeat=3):
    if (u*u+d49*v*v-b49*z*z)%49==0 and any(x%7 for x in (u,v,z)):
        primitive49.append([u,v,z])
assert primitive49==[]
result=dict(scope="Exact field-form arithmetic and finite primitive-conic obstructions; graph-to-form and local embeddings are paper arguments",minimal_polynomial=str(f),
 partitions=[dict(sizes=[12,12,22],norms=[str(g),str(g),str(h)],total_norm=str(G),diagonal_ratio=str(delta),prime=3,hensel_root_mod_p2=4,b_mod_p2=b9,delta_mod_p2=d9,primitive_solutions=primitive,triples_checked=729),
 dict(sizes=[10,12,24],norms=[str(g10),str(g),str(2*g)],total_norm=str(G),diagonal_ratio=str(delta2),prime=7,hensel_root_mod_p2=16,b_mod_p2=b49,delta_mod_p2=d49,primitive_solutions=primitive49,triples_checked=49**3)])
Path(__file__).with_suffix(".json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
