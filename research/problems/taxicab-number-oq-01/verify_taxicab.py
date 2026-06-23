#!/usr/bin/env python3
"""Independent certificate for Ta(2)=1729.

Claim: 1729 is the smallest positive integer expressible as a sum of two
positive cubes in (at least) two distinct ways (unordered, distinct pairs).
  1729 = 1^3 + 12^3 = 9^3 + 10^3.

Tractability fact used by the Lean formalization: for any n <= 1729, every
representation n = a^3 + b^3 with 1 <= a <= b has b^3 <= n <= 1729 < 13^3,
so a, b <= 12. Hence the finite search may be bounded to the 12x12 grid.
"""

def reps(n, cap):
    """Unordered pairs (a,b), 1<=a<=b<=cap, a^3+b^3=n."""
    out = []
    for a in range(1, cap + 1):
        for b in range(a, cap + 1):
            if a**3 + b**3 == n:
                out.append((a, b))
    return out

CAP = 12
assert 12**3 == 1728 and 13**3 == 2197, "cube bound sanity"

# 1) 1729 has exactly two representations within the 12x12 grid.
r1729 = reps(1729, CAP)
print("reps(1729) =", r1729)
assert r1729 == [(1, 12), (9, 10)], r1729

# 2) Minimality: no m < 1729 has >= 2 representations (cap 12 is valid for all m<=1729).
worst = 0
offenders = [m for m in range(1, 1729) if len(reps(m, CAP)) >= 2]
print("m < 1729 with >=2 reps:", offenders)
assert offenders == [], offenders

# 3) Cap-soundness: confirm no representation of any m<=1729 escapes cap 12
#    (i.e. brute force with a generous cap finds nothing new).
GEN = 20
for m in [1729] + list(range(1, 1729)):
    assert reps(m, GEN) == reps(m, CAP), f"cap escape at {m}"

print("CERTIFIED: Ta(2) = 1729; minimal; cube summands <= 12 for all n <= 1729.")
