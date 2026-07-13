#!/usr/bin/env python3
"""Certificate for cube-root-3-irrational-oq-04 Session S27.

Verifies the twenty-first convergent (0-based index 20) of the simple
continued fraction of cbrt3 = 3^(1/3):

    8350315863 / 5789785648  <  cbrt3

This is a LOWER bound (even convergent index), discharged in Lean by the
cubing-iff helper `lt_cbrt3_iff_cube_lt`, i.e. it suffices to show
`(p/q)^3 < 3`, equivalently the exact integer inequality `p^3 < 3 * q^3`.

The script independently:
  1. recomputes cbrt3 to 200 digits via Newton iteration,
  2. extracts the CF partial quotients and confirms a20 = 1,
  3. confirms the convergent recursion p20 = a20*p19 + p18, q20 = a20*q19 + q18,
  4. confirms the exact integer cube-side direction p^3 < 3*q^3.
"""
from decimal import Decimal, getcontext

getcontext().prec = 240

# Newton iteration for cbrt3.
x = Decimal(1.5)
for _ in range(300):
    x = (2 * x + Decimal(3) / (x * x)) / 3

# CF extraction.
a = []
y = x
for _ in range(25):
    ai = int(y)
    a.append(ai)
    frac = y - ai
    if frac == 0:
        break
    y = 1 / frac

assert a[:21] == [1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3, 4, 2, 6, 4, 4, 1], \
    f"CF prefix mismatch: {a[:21]}"
assert a[20] == 1, f"a20 expected 1, got {a[20]}"
assert a[21] == 3, f"a21 expected 3, got {a[21]}"

# Convergents.
hm1, hm2 = 1, 0
km1, km2 = 0, 1
convergents = []
for ai in a:
    h = ai * hm1 + hm2
    k = ai * km1 + km2
    convergents.append((h, k))
    hm2, hm1 = hm1, h
    km2, km1 = km1, k

p18, q18 = convergents[18]
p19, q19 = convergents[19]
p20, q20 = convergents[20]
p21, q21 = convergents[21]

assert (p18, q18) == (1593368375, 1104779927), (p18, q18)
assert (p19, q19) == (6756947488, 4685005721), (p19, q19)
assert (p20, q20) == (8350315863, 5789785648), (p20, q20)
assert (p21, q21) == (31807895077, 22054362665), (p21, q21)

# Recursion with a20 = 1, a21 = 3.
assert p20 == 1 * p19 + p18
assert q20 == 1 * q19 + q18
assert p21 == 3 * p20 + p19
assert q21 == 3 * q20 + q19

# 21st convergent (idx20): LOWER bound <=> p^3 < 3 q^3.
lhs = p20 ** 3
rhs = 3 * q20 ** 3
assert lhs < rhs, "21st: not a valid lower bound"

# 22nd convergent (idx21): UPPER bound <=> 3 q^3 < p^3.
lhs21 = p21 ** 3
rhs21 = 3 * q21 ** 3
assert rhs21 < lhs21, "22nd: not a valid upper bound"

print("CF prefix a0..a21:", a[:22])
print(f"21st convergent (idx20): {p20}/{q20}  (a20 = {a[20]})  LOWER")
print(f"  p^3        = {lhs}")
print(f"  3*q^3      = {rhs}")
print(f"  3*q^3 - p^3 = {rhs - lhs}  (> 0 => lower bound valid)")
print(f"22nd convergent (idx21): {p21}/{q21}  (a21 = {a[21]})  UPPER")
print(f"  p^3        = {lhs21}")
print(f"  3*q^3      = {rhs21}")
print(f"  p^3 - 3*q^3 = {lhs21 - rhs21}  (> 0 => upper bound valid)")
print("CERTIFICATE PASSED: 8350315863/5789785648 < cbrt3 < 31807895077/22054362665")
