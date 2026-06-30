#!/usr/bin/env python3
"""Offline certificate for `cbrt3_a13 = 3` (CubeRoot3IrrationalOQ04A12.lean).

Exact rational propagation of the convergent sandwich
    6193523/4294349 < cbrt3 < 1865358/1293367
through the twelve CF maps x |-> 1/(x - a_i) for a_0..a_12 =
[1,2,3,1,4,1,5,1,1,6,2,5,8], confirming the thirteenth tail lands in
    x_13 in (3/10, 1/3)  =>  1/x_13 in (3, 10/3) subset (3,4)  =>  floor = 3.
"""
from fractions import Fraction as F
lo0, hi0 = F(6193523, 4294349), F(1865358, 1293367)
assert lo0**3 < 3 < hi0**3
subs = [2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8]   # a_1..a_12
loX, hiX = lo0 - 1, hi0 - 1
assert loX > 0 and hiX > 0
loY, hiY = 1/hiX, 1/loX
print(f"y1  in ({loY}, {hiY})")
k = 1
for a in subs[:-1]:
    loX, hiX = loY - a, hiY - a
    assert loX > 0 and hiX > 0, f"x{k+1} not positive"
    loY, hiY = 1/hiX, 1/loX
    k += 1
    print(f"x{k} in ({loX}, {hiX})   y{k} in ({loY}, {hiY})")
loX13, hiX13 = loY - subs[-1], hiY - subs[-1]
print(f"x13 in ({loX13}, {hiX13})")
assert loX13 > 0 and hiX13 > 0
lo_inv, hi_inv = 1/hiX13, 1/loX13
print(f"1/x13 in ({lo_inv}, {hi_inv})")
assert lo_inv >= 3 and hi_inv < 4
assert (loX13, hiX13) == (F(3, 10), F(1, 3))
assert (lo_inv, hi_inv) == (F(3), F(10, 3))
print("PASS: floor(1/x13) = 3 = a_13  (rigorous exact-rational certificate)")
