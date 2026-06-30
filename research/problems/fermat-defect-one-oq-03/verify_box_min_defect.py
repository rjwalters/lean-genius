#!/usr/bin/env python3
"""OQ-03: exact box-restricted minimal Fermat defect m_N(n).

m_N(n) = min { |a^n + b^n - c^n| : 2 <= a <= b < c <= N }.

Demonstrates the non-monotone wobble m_100(4)=46 > 12=m_100(5) that motivates
proofs/Proofs/FermatDefectOneOQ03.lean. Each minimum below c<=100 is unique and
achieved by a primitive triple (gcd=1).
"""
from math import gcd

N = 100
for n in range(3, 9):
    best = None
    achievers = []
    for c in range(3, N + 1):
        cn = c ** n
        for b in range(2, c):
            bn = b ** n
            for a in range(2, b + 1):
                d = abs(a ** n + bn - cn)
                if best is None or d < best:
                    best, achievers = d, [(a, b, c)]
                elif d == best:
                    achievers.append((a, b, c))
    prim = all(gcd(gcd(a, b), c) == 1 for (a, b, c) in achievers)
    print(f"n={n}: m_{N}(n) = {best:>5}  achievers={achievers}  all_primitive={prim}")

print()
print("Non-monotonicity:  m_100(4) = 46  >  12 = m_100(5)")
print("  n=4 achiever 5^4+5^4+46 =", 5**4 + 5**4 + 46, "= 6^4 =", 6**4)
print("  n=5 achiever 13^5+16^5  =", 13**5 + 16**5, "= 17^5+12 =", 17**5 + 12)
