#!/usr/bin/env python3
"""Offline certificate for `cbrt3_a12 = 8` (CubeRoot3IrrationalOQ04A12.lean).

Exact rational (fractions.Fraction) propagation of the convergent sandwich
    597449/414248 < cbrt3 < 1865358/1293367
through the eleven CF maps x |-> 1/(x - a_i) for a_0..a_11 =
[1,2,3,1,4,1,5,1,1,6,2,5], confirming the twelfth tail lands in
    x_12 in (3/25, 1/8)  =>  1/x_12 in (8, 25/3) subset (8,9)  =>  floor = 8.

Each printed (lo,hi) pair is the exact bound that appears in the Lean proof.
Run: python3 verify_a12_floor.py   (PASS prints all bounds + final floor).
"""
from fractions import Fraction as F

lo0, hi0 = F(597449, 414248), F(1865358, 1293367)
assert lo0**3 < 3 < hi0**3, "sandwich must cube-bracket 3"

subs = [2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5]   # a_1..a_11
# y_1 = 1/(cbrt3 - 1)
loX, hiX = lo0 - 1, hi0 - 1
assert loX > 0 and hiX > 0
loY, hiY = 1/hiX, 1/loX
print(f"y1  in ({loY}, {hiY})")
k = 1
for a in subs[:-1]:            # a_1..a_10 -> x_2..x_11, y_2..y_11
    loX, hiX = loY - a, hiY - a
    assert loX > 0 and hiX > 0, f"x{k+1} not positive"
    loY, hiY = 1/hiX, 1/loX
    k += 1
    print(f"x{k} in ({loX}, {hiX})   y{k} in ({loY}, {hiY})")
# final level: x_12 = y_11 - 5
loX12, hiX12 = loY - subs[-1], hiY - subs[-1]
print(f"x12 in ({loX12}, {hiX12})")
assert loX12 > 0 and hiX12 > 0
lo_inv, hi_inv = 1/hiX12, 1/loX12
print(f"1/x12 in ({lo_inv}, {hi_inv})")
assert lo_inv >= 8 and hi_inv < 9, "floor not pinned to 8"
assert (loX12, hiX12) == (F(3, 25), F(1, 8))
assert (lo_inv, hi_inv) == (F(8), F(25, 3))
print("PASS: floor(1/x12) = 8 = a_12  (rigorous exact-rational certificate)")
