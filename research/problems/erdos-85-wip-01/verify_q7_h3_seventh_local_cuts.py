"""Exact rational polynomial dual certificates for two fixed-psi3 local cuts."""
import json
from pathlib import Path
import sympy as s
from verify_q7_h3_local_galois_measures import roots, Q, Gi, target

rows=json.loads(Path(__file__).with_name('q7_h3_seventh_local_cuts.json').read_text())
assert [r['type'] for r in rows]==[[1,1,2,1],[1,2,2,0]]
for row in rows:
    a=row['type'];tar=target(*a);u=s.Matrix([[1,a[0]]]);q7=(u*Q**7*Gi*u.T)[0]
    bounds=[]
    for sign,dual in zip([1,-1],row['duals'],strict=True):
        y=list(map(s.Rational,dual));assert len(y)==7
        for r in roots:
            slack=s.simplify(sign*r**7-sum(y[j]*r**j for j in range(7)))
            assert slack.is_nonnegative is True
        bounds.append(q7+sign*sum(y[j]*tar[j] for j in range(7)))
    assert bounds==list(map(s.Rational,row['bounds']))
    low,high=bounds;left,right=row['excluded_even_gap']
    assert left%2==0 and right==left+2 and left<low<=high<right
    print(f'PASS local type {a}: {left} < (C^7)vv < {right}; incompatible with even integer diagonal')
print('Only these two local types for the specified residual polynomial are excluded; no full-profile exclusion.')
