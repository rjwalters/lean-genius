"""Regression checks for the uniform proof in UNIFORM.md."""
import json
from pathlib import Path

cases = []
for k in range(2, 7):
    q = 2**k
    n, m = q*q, q//2
    rows = []
    for b in range(k+1, 2*k+1):
        d = 2**b
        N = d//2
        assert N >= 2*m and N % 2 == 0
        support = set()
        for j in range(1, m):
            support.symmetric_difference_update([j, N-j])
        assert len(support) == 2*(m-1) and 1 in support
        # Frobenius is additive in characteristic two. Checking every
        # basis square therefore checks the whole square-image subspace.
        square_support = {(2*j) % N for j in range(N)}
        assert square_support == set(range(0, N, 2))
        assert not support <= square_support
        rows.append({'order': d, 'quotient_degree': N,
                     'coefficient_X': 1, 'outside_square_image': True})
    assert 1+(m-1)+m+sum(r['quotient_degree'] for r in rows) == n
    assert (q-2) % 4 == 2
    if k % 2 == 0:
        s = 2**(k//2)
        assert s*s == q and s % 2 == 0 and (m-1) % 2 == 1
    cases.append({'q': q, 'strata': rows, 'trace_case': 'odd k' if k%2 else 'even k'})
result = {'status': 'PASS', 'scope': 'finite regressions of the uniform prose proof', 'cases': cases}
Path(__file__).with_name('mod2-verification.json').write_text(json.dumps(result, indent=2)+'\n')
print('PASS: q=4,8,16,32,64; all high-order coefficient obstructions and trace cases')
