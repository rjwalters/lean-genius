"""Exact cyclotomic norm certificates; no adjacency or defect matrices."""
import json
from pathlib import Path
import sympy as s

x = s.Symbol('x')
primes = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
assert all(all(p % d for d in range(2, s.integer_nthroot(p, 2)[0]+1)) for p in primes)
results = []
for q in [16, 64]:
    n, m = q*q, q//2
    root, square = s.integer_nthroot(q, 2)
    assert square and root % 2 == 0 and (m-1) % 2 == 1
    assert not s.integer_nthroot(q-2, 2)[1]
    C = [s.Poly(2, x), s.Poly(x, x)]
    for j in range(2, m):
        C.append(s.Poly(x, x)*C[-1]-C[-2])
    interval = sum(C[1:], s.Poly(0, x))
    f = s.Poly(x, x)
    strata = []
    for b in range(2, n.bit_length()):
        d = 2**b
        if b > 2:
            f = f*f-2
        assert f.degree() == d//4
        g = s.Poly(q-(0 if d == n else 2), x)-interval
        if d <= m:
            assert g.rem(f) == s.Poly(q, x)
            continue
        if d == q:
            assert g.rem(f) == s.Poly(q-2, x)
            continue
        witness = None
        for p in primes:
            residue = int(s.resultant(f.as_expr(), g.as_expr(), x, modulus=p)) % p
            if residue and pow(residue, (p-1)//2, p) == p-1:
                witness = {'prime': p, 'norm_residue': residue}
                break
        assert witness is not None, (q, d)
        strata.append({'order': d, 'real_degree': f.degree(), **witness})
    # Order two also lies in the q-eigenspace: its paired-step sum is -2.
    assert sum(2*(-1)**j for j in range(1, m)) == -2
    assert 1+(m-1)+m+sum(2*r['real_degree'] for r in strata) == n
    # trace A / sqrt(q) = sqrt(q) + an odd integer cannot vanish.
    results.append({'q': q, 'q_eigenvalue_multiplicity': m-1,
                    'higher_strata': strata, 'trace_obstruction': True})
out = {'status': 'PASS', 'scope': 'interval circulant defects at q=16,64 only',
       'cases': results}
Path(__file__).with_name('verification.json').write_text(json.dumps(out, indent=2)+'\n')
print(json.dumps(out, indent=2))
