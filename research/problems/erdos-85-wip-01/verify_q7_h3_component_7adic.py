"""Exact arithmetic for the conditional H3 defect partition10+12+24 obstruction."""
import json
from itertools import product
from pathlib import Path
import sympy as s

a = s.symbols('a')
f = a*a - 7*a + 3
red = lambda v: s.rem(s.expand(v), f, a)
# Component (size, per-high support count, selected-pair degree).
params = [(10, 2, 2), (12, 2, 0), (24, 4, 0)]
norms = [red(n*a*a - 2*a*(3*k) + 3*k + 3*r) for n, k, r in params]
p, q, r = norms
assert norms == [58*a-18, 72*a-30, 144*a-60]
assert r == 2*q
G = red(p+q+r)
assert G == 274*a-108
M = s.diag(*norms)
v1 = s.Matrix([0, 2, -1])
v2 = s.Matrix([3*q, -p, -p])
one = s.ones(3, 1)
for v in (v1, v2):
    assert red((v.T*M*one)[0]) == 0
assert red((v1.T*M*v2)[0]) == 0
delta = red(p*G/2)
assert delta == 50024*a-22866
assert red((v1.T*M*v1)[0]-6*q) == 0
assert red((v2.T*M*v2)[0]-6*q*delta) == 0
assert red(a*(7-a)) == 3
assert f.subs(a, 16) % 49 == 0
assert s.diff(f, a).subs(a, 16) % 7 != 0
b49 = int((7-a).subs(a, 16) % 49)
d49 = int(delta.subs(a, 16) % 49)
assert (b49, d49) == (40, 35)
assert 5 not in {x*x % 7 for x in range(7)}
primitive = []
for u, v, z in product(range(49), repeat=3):
    if (u*u+d49*v*v-b49*z*z) % 49 == 0 and any(x % 7 for x in (u,v,z)):
        primitive.append([u,v,z])
assert primitive == []
result = dict(scope='Exact field-form arithmetic and primitive mod49 obstruction only; graph-to-form and Q7 embedding are paper proofs',
              minimal_polynomial=str(f), component_parameters=params,
              norms=[str(x) for x in norms], total_norm=str(G),
              diagonal_ratio=str(delta), hensel_root_mod49=16,
              b_mod49=b49, delta_mod49=d49,
              triples_checked=49**3, primitive_solutions_mod49=primitive)
Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
