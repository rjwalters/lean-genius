#!/usr/bin/env python3
"""
Build-free certification of the second-supplementary-law EXPONENTIAL form
    legendreSym p 2  =  (-1)^((p^2 - 1)/8)        (odd prime p)

This is the remaining documented gap for quadratic-reciprocity-oq-03-oq-01
(S1 proved the chi8 form, S2 the residue-criterion form). The Lean proof
(QuadraticReciprocityOQ03OQ01Exp.lean) reduces it to:

  chi8(p mod 8)  =  (-1)^((p^2-1)/8)

via a 4-way case split on p % 8 in {1,3,5,7}, in each case exhibiting an
EXACT decomposition  p^2 = 8*(8 m^2 + 2 m r' + d) + 1  (no Nat subtraction),
so that  (p^2-1)/8 = 8 m^2 + 2 m r' + d  and the sign is read off the parity
of that integer.  This script re-derives -- not plugs in -- every identity
the Lean lemma encodes, and exits non-zero on any mismatch.

Cross-checks (sympy symbolic + brute force):
  (A) chi8 value table on residues 1,3,5,7 is  +1,-1,-1,+1.
  (B) For p = 8 m + r (r in {1,3,5,7}) the exact ring identity
          p^2 == 8*(8 m^2 + 2 m r + d_r) + 1,   d = {1:0, 3:1, 5:3, 7:6}
      holds symbolically in m.
  (C) Hence (p^2-1)/8 == 8 m^2 + 2 m r + d_r, and its parity equals d_r mod 2,
      i.e. parity 0,1,1,0 on residues 1,3,5,7 -- matching chi8 via (-1)^parity.
  (D) End-to-end brute force over all odd primes p < 20000:
          legendre(2,p) == (-1)**(((p*p-1)//8) % 2)  and  == chi8(p%8).
  (E) The even Even/Odd witnesses used in Lean are exact:
          8 m^2 + 2 m r + d  =  2*w + (d mod 2)   with the stated w(m).
"""
import sys
import sympy as sp

FAIL = 0

def check(name, cond):
    global FAIL
    status = "PASS" if cond else "FAIL"
    if not cond:
        FAIL += 1
    print(f"  [{status}] {name}")

m = sp.symbols('m', integer=True, nonnegative=True)

# chi8 value on odd residues, and the exponent-data d_r = (r^2-1)//8
chi8 = {1: 1, 3: -1, 5: -1, 7: 1}
d_r = {r: (r * r - 1) // 8 for r in (1, 3, 5, 7)}      # 0,1,3,6
# Even/Odd witness w_r(m) so that 8 m^2 + 2 m r + d_r = 2 w + (d_r mod 2)
w_r = {
    1: 4 * m**2 + m,          # 8m^2+2m       = 2(4m^2+m)
    3: 4 * m**2 + 3 * m,      # 8m^2+6m+1     = 2(4m^2+3m)+1
    5: 4 * m**2 + 5 * m + 1,  # 8m^2+10m+3    = 2(4m^2+5m+1)+1
    7: 4 * m**2 + 7 * m + 3,  # 8m^2+14m+6    = 2(4m^2+7m+3)
}

print("(A) chi8 value table on residues {1,3,5,7}:")
check("chi8 = +1,-1,-1,+1", [chi8[r] for r in (1, 3, 5, 7)] == [1, -1, -1, 1])
check("d_r = (r^2-1)/8 = 0,1,3,6", [d_r[r] for r in (1, 3, 5, 7)] == [0, 1, 3, 6])
check("chi8(r) = (-1)^(d_r)", all(chi8[r] == (-1) ** d_r[r] for r in (1, 3, 5, 7)))

print("(B) exact ring identity  p^2 == 8*(8 m^2 + 2 m r + d_r) + 1:")
for r in (1, 3, 5, 7):
    p = 8 * m + r
    lhs = sp.expand(p**2)
    rhs = sp.expand(8 * (8 * m**2 + 2 * m * r + d_r[r]) + 1)
    check(f"r={r}:  (8m+{r})^2 == 8*(8m^2+{2*r}m+{d_r[r]})+1", sp.simplify(lhs - rhs) == 0)

print("(C) exponent value and parity:")
for r in (1, 3, 5, 7):
    # (p^2-1)/8 == 8 m^2 + 2 m r + d_r  (exact integer division, certified by (B))
    expo = 8 * m**2 + 2 * m * r + d_r[r]
    parity_expected = d_r[r] % 2
    # parity is constant in m since 8 m^2 + 2 m r are even
    check(f"r={r}: parity((p^2-1)/8) == {parity_expected}",
          sp.simplify((expo - parity_expected) / 2 - sp.Rational(1, 1) * 0) is not None
          and all(int((8 * mm**2 + 2 * mm * r + d_r[r]) % 2) == parity_expected
                  for mm in range(0, 50)))

print("(D) Even/Odd witness exactness  8m^2+2mr+d == 2 w_r + (d mod 2):")
for r in (1, 3, 5, 7):
    expo = 8 * m**2 + 2 * m * r + d_r[r]
    check(f"r={r}: == 2*w_r(m) + {d_r[r] % 2}",
          sp.simplify(expo - (2 * w_r[r] + (d_r[r] % 2))) == 0)

print("(E) end-to-end brute force over odd primes p < 20000:")
def legendre(a, p):
    ls = pow(a % p, (p - 1) // 2, p)
    return -1 if ls == p - 1 else ls  # 0,1, or -1

bad = []
for p in sp.primerange(3, 20000):
    lhs = legendre(2, p)
    rhs_pow = (-1) ** (((p * p - 1) // 8) % 2)
    rhs_chi = chi8[p % 8]
    if not (lhs == rhs_pow == rhs_chi):
        bad.append((p, lhs, rhs_pow, rhs_chi))
check(f"legendre(2,p) == (-1)^((p^2-1)/8) == chi8(p%8) for all odd primes < 20000 ({len(bad)} mismatches)",
      not bad)
if bad:
    print("   first mismatches:", bad[:5])

print()
if FAIL:
    print(f"RESULT: {FAIL} CHECK(S) FAILED")
    sys.exit(1)
print("RESULT: ALL CHECKS PASS")
