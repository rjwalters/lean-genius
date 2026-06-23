#!/usr/bin/env python3
"""
Certificate for divisibility-truncation-general-oq-01-oq-01.

Claim (Combined Divisibility Theorem): for d = s*m with
  - s | 10^k          (the 2^a*5^b part; tested via last-k-digits)
  - gcd(s, m) = 1
  - gcd(m, 10) = 1     (the osculator part)
  - m | 10c - 1        (c is the signed osculator of m)
then for all n:
    d | n   <=>   (s | n % 10^k)  AND  (m | n//10 + c*(n%10)).

We verify both the side conditions and the iff over a large range of n,
including the new cases d in {6, 12, 14, 35} from the Lean file.
"""

from math import gcd

# (label, s, m, c, k)  -> d = s*m
CASES = [
    ("6  = 2*3 ", 2, 3, 1, 1),
    ("12 = 4*3 ", 4, 3, 1, 2),
    ("14 = 2*7 ", 2, 7, 5, 1),
    ("15 = 3*5 ", 5, 3, 1, 1),   # s=5 is the 2/5-part, m=3
    ("35 = 5*7 ", 5, 7, 5, 1),
    ("18 = 2*9 ", 2, 9, 1, 1),   # m=9 coprime to 10, osc c=1 (9|10*1-1=9)
    ("28 = 4*7 ", 4, 7, 5, 2),
    ("21 = 1*21", 1, 21, 19, 0), # pure coprime case (s=1, k=0): osc 21|10*19-1=189=9*21
    ("50 =50*1 ", 50, 1, 0, 2),  # pure last-k-digits case (m=1)
]

NMAX = 200_000


def check_side_conditions(s, m, c, k):
    assert s % gcd(s, 10**k if k > 0 else 1) == s or (10**k) % s == 0, "s | 10^k fails"
    assert (10**k) % s == 0, f"s={s} does not divide 10^{k}"
    assert gcd(s, m) == 1, f"gcd(s={s}, m={m}) != 1"
    assert gcd(m, 10) == 1, f"gcd(m={m}, 10) != 1"
    assert (10 * c - 1) % m == 0, f"m={m} does not divide 10c-1 (c={c})"


def combined_test(n, s, m, c, k):
    left = (n % (10**k)) % s == 0
    osc = (n // 10) + c * (n % 10)
    right = osc % m == 0
    return left and right


all_ok = True
for label, s, m, c, k in CASES:
    d = s * m
    try:
        check_side_conditions(s, m, c, k)
    except AssertionError as e:
        print(f"[{label}] SIDE-CONDITION FAIL: {e}")
        all_ok = False
        continue
    mism = 0
    for n in range(NMAX):
        if (n % d == 0) != combined_test(n, s, m, c, k):
            mism += 1
            if mism <= 3:
                print(f"[{label}] MISMATCH at n={n}: dvd={n%d==0} test={combined_test(n,s,m,c,k)}")
    status = "PASS" if mism == 0 else f"FAIL ({mism} mismatches)"
    print(f"[{label}] d={d:3d}  s={s:2d} m={m:2d} c={c:2d} k={k}  range[0,{NMAX})  {status}")
    all_ok = all_ok and (mism == 0)

print()
print("ALL CASES PASS" if all_ok else "SOME CASES FAILED")
