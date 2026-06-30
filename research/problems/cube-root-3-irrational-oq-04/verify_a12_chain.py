from fractions import Fraction as F
from decimal import Decimal, getcontext
getcontext().prec = 80

# High-precision cbrt3 for CF sequence sanity
cbrt3 = Decimal(3) ** (Decimal(1)/Decimal(3))
x = cbrt3; qs=[]
for _ in range(13):
    a=int(x); qs.append(a); x = Decimal(1)/(x-a)
print("CF a0..a12 (decimal):", qs)
expect=[1,2,3,1,4,1,5,1,1,6,2,5,8]
print("matches OEIS A002945 prefix:", qs==expect)

# RIGOROUS interval propagation using the EXACT helper sandwich for a12=8.
# Sandwich present in helper file:
lo = F(597449,414248)   # 5..lower < cbrt3
hi = F(1865358,1293367) # cbrt3 < ..upper  (S14a helper)
# verify both are valid bounds by cube direction
print("lo^3 < 3 :", lo**3 < 3, " (diff num sign)", (3 - lo**3))
print("hi^3 > 3 :", hi**3 > 3, " (diff)", (hi**3 - 3))

# Partial quotients consumed AFTER the initial (cbrt3 - 1):
# x0 = cbrt3; we subtract 1 then invert, etc.
# Full sequence of a_i for i=0..11 to reach the 1/x that floors to a12.
seq = [1,2,3,1,4,1,5,1,1,6,2,5]  # a0..a11; final 1/x gives a12
# Interval map: start I=[lo,hi]; repeatedly I <- 1/(I - a) where subtraction
# then reciprocal. For monotone decreasing reciprocal on positive interval,
# 1/[u,v] = [1/v,1/u].
def step(I,a):
    u,v = I
    u2,v2 = u-a, v-a
    assert u2>0, f"interval crossed 0 at a={a}: {u2}"
    # reciprocal flips order
    return (F(1,v2), F(1,u2))
I=(lo,hi)
for a in seq:
    I=step(I,a)
u,v=I
print("final 1/x interval:", float(u), float(v))
print("floor forced =", "8" if (u>=8 and v<9) else f"NOT 8 -> [{u},{v}]")
print("8 <= u :", u>=8, "  v < 9 :", v<9)
