"""S15a verification: a13 = 3 (14th partial quotient) and the corrected
p14 lower-bound convergent for the simple CF of cbrt3.

Catches the a14 = 4 -> a14 = 3 math-correction. Run: python3 verify_a13_sandwich.py
"""
from fractions import Fraction as F
from decimal import Decimal, getcontext
getcontext().prec = 120

# High-precision cbrt3 via Newton; independent CF sequence.
three = Decimal(3); x = Decimal('1.44224957')
for _ in range(25):
    x = (2 * x + three / (x * x)) / 3
cbrt3 = x
v = cbrt3; qs = []
for _ in range(16):
    a = int(v); qs.append(a); v = Decimal(1) / (v - a)
assert qs[:15] == [1,2,3,1,4,1,5,1,1,6,2,5,8,3,3], qs
print("CF a0..a14 =", qs[:15], "(a13=3, a14=3 -- NOT a14=4)")

# Corrected fifteenth convergent p14/q14 = (a14*p13+p12)/(a14*q13+q12), a14=3.
p14, q14 = 3*1865358 + 597449, 3*1293367 + 414248
assert (p14, q14) == (6193523, 4294349)
assert p14**3 < 3 * q14**3, "p14 must be BELOW cbrt3 (even index)"
# The wrong a14=4 convergent is ABOVE -> would fail as a lower bound:
pw, qw = 4*1865358 + 597449, 4*1293367 + 414248   # 8058881/5587716
assert pw**3 > 3 * qw**3, "wrong a14=4 convergent is ABOVE cbrt3"
print(f"correct lower bound p14/q14 = {p14}/{q14} (below); "
      f"wrong a14=4 gives {pw}/{qw} (above, invalid)")

# Rigorous a13 floor via exact interval propagation through a0..a12.
lo, hi = F(6193523, 4294349), F(1865358, 1293367)   # p14 below, p13 above
def step(I, a):
    u, v = I; u2, v2 = u - a, v - a
    assert u2 > 0, f"interval crossed 0 at a={a}"
    return (F(1, v2), F(1, u2))
I = (lo, hi)
for a in [1,2,3,1,4,1,5,1,1,6,2,5,8]:
    I = step(I, a)
u, v = I
assert u >= 3 and v < 4, (u, v)
print(f"a13 floor forced: 1/x in [{float(u)}, {float(v)}) subset [3,4) => a13 = 3  CERTIFICATE PASSED")
