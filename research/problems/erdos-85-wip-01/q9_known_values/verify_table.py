"""Check the arithmetic bridge; this is not a verification of the cited proofs."""
import json
import math
from pathlib import Path

root = Path(__file__).resolve().parent
lower = {n: n + 1 for n in range(2, 100)}
upper = {n: n + math.isqrt(n - 2) + 2 for n in range(2, 100)}
why = {n: "trivial" for n in lower}

def exact(n, value, source):
    assert lower[n] <= value <= upper[n], (n, value)
    lower[n] = upper[n] = value
    why[n] = source

for q in (8, 9):
    for offset in (0, 1):
        exact(q*q + offset, q*q + q + 1 + offset, "Parsons1975")
for t in range(1, 10):
    if t != 8:
        exact(64-t, 73-t, "Parsons1976 even q=8")
for t in (2, 4, 6):
    exact(72-t, 81-t, "ZCC2017 Some values q=9")
for t in (1, 2, 3, 4, 6):
    exact(81-t, 91-t, "ZCC2017 Polarity q=9")
upper[67] = 76  # Boza Theorem4, m=8; independent of his r76 citation.

# Monotonicity is for r, NOT for the Erdos threshold f.
# Chen: r(n-1) >= r(n)-2.
# Boza Cor7 is used only at exact, independently traced seed values.
for n in (78, 80, 81, 82):
    assert lower[n] == upper[n]
    target = 2*n + 1 - lower[n]
    lower[target] = max(lower[target], n)
    why[target] = f"Boza Cor7 at r({n})={lower[n]}"
changed = True
while changed:
    changed = False
    for n in range(3, 100):
        if lower[n] < lower[n-1]:
            lower[n] = lower[n-1]
            why[n] = f"monotonicity from r({n-1})"
            changed = True
        if lower[n-1] < lower[n]-2:
            lower[n-1] = lower[n]-2
            why[n-1] = f"Chen from r({n})"
            changed = True
    assert all(lower[n] <= upper[n] for n in lower)

reported = dict(lower)
for n, value in {67:76, 73:83, 74:84, 76:86}.items():
    reported[n] = value

rows = []
for N in range(73, 92):
    def threshold_bounds(L):
        witnesses = [d for d in range(1, N-1) if L[N-d] > N]
        exclusions = [d for d in range(1, N-1) if upper[N-d] <= N]
        d = max(witnesses)
        excluded = min(exclusions)
        return d+1, excluded, d, N-d, N-excluded
    lo, hi, d, witness_n, exclusion_n = threshold_bounds(lower)
    rep_lo, rep_hi, *_ = threshold_bounds(reported)
    rows.append(dict(N=N, audited_f=[lo, hi], reported_f=[rep_lo, rep_hi],
                     lower_bridge=dict(d=d, n=witness_n, r_lower=lower[witness_n]),
                     upper_bridge=dict(d=hi, n=exclusion_n, r_upper=upper[exclusion_n])))

assert [r['N'] for r in rows if r['audited_f'] == [9, 9]] == [73,74,76,77,79]
assert [r['N'] for r in rows if r['audited_f'] == [10, 10]] == [84,86,87,88,89,90,91]
assert rows[2]['audited_f'] == [8,9]
assert [r['N'] for r in rows if r['audited_f'] == [9,10]] == [78,80,81,82,83,85]
assert upper[70] == 79
result = {'scope':'arithmetic only; source proofs are literature premises',
          'ramsey_bounds':{str(n):[lower[n],upper[n]] for n in range(64,83)}, 'rows':rows}
(root/'table-results.json').write_text(json.dumps(result, indent=2)+'\n')
for row in rows:
    print(row['N'], row['audited_f'], row['reported_f'])
