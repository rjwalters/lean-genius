#!/usr/bin/env python3
"""
ORIENT verifier for wilsons-theorem-oq-02-ext-oq-02:
"Does Gauss-Wilson extend to rings of integers O_K of number fields?
 Characterize when prod over the unit group equals -1, analogous to ZMod."

Strategy (exact integer arithmetic, no floats):
  O_K for an imaginary quadratic field = Z[alpha], alpha a root of a monic
  quadratic  x^2 = t*x + u  (the minimal polynomial of the ring generator).
  We model the FINITE residue ring  R = O_K / (m)  for a rational integer m
  as  (Z/m)[x] / (x^2 - t*x - u),  whose elements are pairs (a,b) <-> a + b*alpha,
  a,b in Z/m.  This is the genuine analogue of Z/n = Z/(n).

  For each R we:
    * enumerate the unit group  R^x  (elements with a multiplicative inverse),
    * compute  P = prod_{u in R^x} u,
    * count involutions  T = #{u in R^x : u^2 = 1, u != 1},
    * check Miller's theorem (the just-merged general-abelian result #24251):
        P = the unique involution if T == 1, else P = 1.
    * check the Gauss-Wilson characterization:
        P = -1  iff  R^x has a UNIQUE involution AND that involution is -1.

We also handle PRIME ideals whose residue ring is a finite FIELD F_q
(q = p^f), where R^x is cyclic of order q-1, to exhibit the char-2 edge
case (q = 2^f) where -1 = +1 and the product is +1, breaking the naive
"always -1" guess.
"""

from itertools import product as iproduct

# ---- ring O_K/(m) = (Z/m)[x]/(x^2 - t x - u) ----------------------------

def make_ring(t, u, m):
    """Return (elements, mul, one, neg_one) for (Z/m)[x]/(x^2 - t x - u)."""
    def mul(p, q):
        a, b = p
        c, d = q
        # (a+b x)(c+d x) = ac + (ad+bc) x + bd x^2 ; x^2 = t x + u
        lo = (a * c + b * d * u) % m
        hi = (a * d + b * c + b * d * t) % m
        return (lo, hi)
    elems = [(a, b) for a in range(m) for b in range(m)]
    one = (1 % m, 0)
    neg_one = ((-1) % m, 0)
    return elems, mul, one, neg_one

def units_of(elems, mul, one):
    us = []
    eset = set(elems)
    for x in elems:
        # x is a unit iff exists y with x*y = one
        for y in elems:
            if mul(x, y) == one:
                us.append(x)
                break
    return us

def analyze(name, t, u, m):
    elems, mul, one, neg_one = make_ring(t, u, m)
    us = units_of(elems, mul, one)
    # product of all units
    P = one
    for x in us:
        P = mul(P, x)
    # involutions (u^2 = 1, u != 1)
    invs = [x for x in us if mul(x, x) == one and x != one]
    T = len(invs)
    # Miller prediction
    if T == 1:
        miller_pred = invs[0]
    else:
        miller_pred = one
    miller_ok = (P == miller_pred)
    # characterization: P == -1 iff unique involution and it is -1
    char_pred_minus1 = (T == 1 and invs[0] == neg_one)
    P_is_minus1 = (P == neg_one)
    # note: when m==2 (or 2 | m and ring char issues) -1 may equal +1
    minus_eq_plus = (neg_one == one)
    char_ok = (P_is_minus1 == char_pred_minus1) or minus_eq_plus and (P == one)
    status = "OK " if (miller_ok and char_ok) else "FAIL"
    print(f"[{status}] {name:18s} m={m:2d} |Rx|={len(us):4d} "
          f"#inv={T} P={P} (-1={neg_one}) "
          f"Miller={'y' if miller_ok else 'N'} "
          f"P=-1?{'y' if P_is_minus1 else 'n'} pred-1?{'y' if char_pred_minus1 else 'n'}")
    return miller_ok and char_ok

# ---- finite field F_q residue (prime ideal case) ------------------------

def analyze_field_prime(p):
    """Residue field F_p (inert/ramified-degree-1 or split prime, q=p)."""
    # R^x = (Z/p)^x cyclic order p-1
    us = list(range(1, p))
    P = 1
    for x in us:
        P = (P * x) % p
    invs = [x for x in us if (x * x) % p == 1 and x != 1]
    T = len(invs)
    neg1 = (p - 1) % p
    miller_pred = invs[0] if T == 1 else 1
    miller_ok = (P == miller_pred)
    Pm1 = (P == neg1)
    char_pred = (T == 1 and invs[0] == neg1)
    # char-2 degeneracy: when -1 == +1 (p == 2) the statement "P = -1" is
    # the same as "P = 1", so the dichotomy is vacuous and always holds.
    char_ok = (Pm1 == char_pred) or (neg1 == 1 and P == 1)
    status = "OK " if (miller_ok and char_ok) else "FAIL"
    print(f"[{status}] F_{p:<3d} (residue field)     |Fx|={p-1:4d} "
          f"#inv={T} P={P} Miller={'y' if miller_ok else 'N'} P=-1?{'y' if Pm1 else 'n'}")
    return miller_ok and char_ok


if __name__ == "__main__":
    print("=== Reading B: residue rings O_K/(m), the genuine ZMod analogue ===")
    # Gaussian integers Z[i]: alpha=i, x^2 = -1  => t=0, u=-1
    # Eisenstein Z[w], w^2 = -w - 1 (w primitive cube root): t=-1, u=-1
    # Z[sqrt(-2)]: alpha^2 = -2 => t=0, u=-2
    rings = [
        ("Z[i] (x^2=-1)",      0, -1),
        ("Z[w] (x^2=-x-1)",   -1, -1),
        ("Z[sqrt-2](x^2=-2)",  0, -2),
    ]
    allok = True
    for name, t, u in rings:
        for m in range(2, 12):
            allok &= analyze(name, t, u, m)
        print()

    print("=== Char-2 residue FIELDS (the dichotomy-breaking edge) ===")
    for p in [2, 3, 5, 7]:
        allok &= analyze_field_prime(p)
    # F_4, F_8 (q=2^f): unit group odd order => no involution => product = 1, not -1
    # represent F_4 = F_2[x]/(x^2+x+1): t=-1=1, u=-1=1 mod 2
    print("  (F_4: residue ring Z[w]/(2) below — char 2, q=4, q-1=3 odd)")
    analyze("F_4 = Z[w]/(2)", -1, -1, 2)

    print()
    print("ALL CHECKS PASS" if allok else "SOME CHECKS FAILED")
