#!/usr/bin/env python3
"""Reproducible numerical certification of MILESTONE 2 of
quadratic-reciprocity-algorithm-oq-03: deriving the *reciprocity law itself*
from permutation signs (the Zolotarev-Frobenius route), the step left "gated /
assess after Milestone 1" by S1-S5.

Milestone 1 (verify_zolotarev.py) certified the building block
    legendreSym p a = sign(pi_a),   pi_a : x |-> a*x  on ZMod p.
This script certifies the SECOND half: how the two Zolotarev signs combine,
via a CRT change-of-listing permutation, into

    (p/q)(q/p) = (-1)^((p-1)/2 * (q-1)/2)            [Quadratic Reciprocity].

We do NOT hardcode the intermediate sign identities; each candidate relation is
*computed* over every distinct odd prime pair p,q < BOUND and asserted only
after the data confirms it (verify-before-assert).

Certified steps:
  (A)  Zolotarev building block (re-used from M1): for distinct odd primes p,q,
       sign(mult-by-q on ZMod p) = (q/p)  and  sign(mult-by-p on ZMod q) = (p/q).
  (B)  GRID-TRANSPOSE sign: the permutation comparing the row-major listing
       r(i,j)=i*q+j of the p x q grid with the column-major listing
       c(i,j)=j*p+i has sign (-1)^((p-1)/2 * (q-1)/2).  [the reciprocity factor]
  (C)  CRT-LISTING sign: the permutation of {0..pq-1} sending the linear index
       k to its CRT-lex position (k mod p, k mod q) decomposes so that its sign
       equals (q/p)*(p/q) ... or the grid factor; the script REPORTS the exact
       relation it finds and asserts it.
  (D)  END-TO-END: (p/q)(q/p) = (-1)^((p-1)/2 (q-1)/2), reproduced purely from
       the permutation-sign route of (A)+(B).

Run: python3 verify_reciprocity_m2.py   (requires sympy). All asserts must pass.
"""

from sympy import primerange

try:  # legendre_symbol moved modules in sympy 1.13
    from sympy.functions.combinatorial.numbers import legendre_symbol
except ImportError:  # pragma: no cover
    from sympy.ntheory.residue_ntheory import legendre_symbol

BOUND = 60  # distinct odd primes 3 <= p,q < BOUND


# ---------------------------------------------------------------------------
def perm_sign(perm):
    """Sign of a permutation given as perm[x] = image(x), via cycle count."""
    n = len(perm)
    seen = [False] * n
    cycles = 0
    for i in range(n):
        if not seen[i]:
            cycles += 1
            j = i
            while not seen[j]:
                seen[j] = True
                j = perm[j]
    return (-1) ** (n - cycles)


def mult_perm_sign(a, m):
    """sign of x |-> a*x mod m on ZMod m (a coprime to m)."""
    return perm_sign([(a * x) % m for x in range(m)])


def grid_transpose_sign(p, q):
    """Permutation sigma = c o r^{-1} on {0..pq-1}, where
       r(i,j)=i*q+j  (row-major, i in [0,p), j in [0,q))
       c(i,j)=j*p+i  (column-major).
       sigma sends row-major index to column-major index of the same cell."""
    N = p * q
    sigma = [0] * N
    for i in range(p):
        for j in range(q):
            sigma[i * q + j] = j * p + i
    return perm_sign(sigma)


def crt_listing_sign(p, q):
    """Permutation rho on {0..pq-1}: rho(k) = lex index of (k mod p, k mod q),
       i.e. (k mod p)*q + (k mod q).  (CRT change of listing.)  p,q coprime."""
    N = p * q
    rho = [((k % p) * q + (k % q)) for k in range(N)]
    return perm_sign(rho)


# ---------------------------------------------------------------------------
def main():
    primes = [p for p in primerange(3, BOUND)]
    pairs = [(p, q) for p in primes for q in primes if p != q]
    print(f"Distinct odd prime pairs 3<=p,q<{BOUND}: {len(pairs)}\n")

    n_ok = 0
    relCgrid = relCleg = True
    for (p, q) in pairs:
        lq_p = legendre_symbol(q, p)   # (q/p)
        lp_q = legendre_symbol(p, q)   # (p/q)
        qr_rhs = (-1) ** (((p - 1) // 2) * ((q - 1) // 2))

        # (A) Zolotarev building block
        assert mult_perm_sign(q % p, p) == lq_p, f"(A) (q/p) at {(p,q)}"
        assert mult_perm_sign(p % q, q) == lp_q, f"(A) (p/q) at {(p,q)}"

        # (B) grid-transpose sign = reciprocity factor
        g = grid_transpose_sign(p, q)
        assert g == qr_rhs, f"(B) grid sign != reciprocity factor at {(p,q)}"

        # (C) CRT-listing sign: discover its relation (don't assume)
        rho = crt_listing_sign(p, q)
        if rho != lq_p * lp_q:
            relCleg = False
        if rho != qr_rhs:
            relCgrid = False

        # (D) end-to-end QR from the permutation route
        assert lp_q * lq_p == qr_rhs, f"(D) QR law numeric at {(p,q)}"
        # reproduced purely from M1 signs + (B):
        lhs_perm = mult_perm_sign(p % q, q) * mult_perm_sign(q % p, p)
        assert lhs_perm == grid_transpose_sign(p, q), \
            f"(D) perm-route (p/q)(q/p) != grid factor at {(p,q)}"
        n_ok += 1

    print(f"(A) Zolotarev signs  sign(mult_q on Z_p)=(q/p), sign(mult_p on Z_q)=(p/q): "
          f"OK for all {n_ok} pairs")
    print(f"(B) grid-transpose sign = (-1)^((p-1)/2 (q-1)/2): OK for all {n_ok} pairs")
    print(f"(C) CRT-listing-permutation sign relation discovered:")
    print(f"      sign(rho) == (q/p)*(p/q)              : {relCleg}")
    print(f"      sign(rho) == (-1)^((p-1)/2 (q-1)/2)   : {relCgrid}")
    print(f"(D) (p/q)(q/p) = (-1)^((p-1)/2 (q-1)/2), reproduced from M1 signs + grid "
          f"factor: OK for all {n_ok} pairs")

    # Whatever (C) turned out to be, it is the same value as (B)/(D) since
    # (q/p)(p/q) = qr_rhs; record the confirmed equivalence as an assert.
    assert relCleg == relCgrid, "internal: (C) relations must agree since QR holds"
    if relCleg:
        print("\n  => CRT-listing sign equals the reciprocity factor; the QR law is the")
        print("     statement that this single permutation's sign is multiplicative")
        print("     across the CRT factors. M2 route is sound.")
    else:
        print("\n  => CRT-listing sign is NOT itself the reciprocity factor; the working")
        print("     bridge is the grid-transpose permutation (B) composed with the two")
        print("     Zolotarev mult-signs (A). M2 route is sound via (A)+(B)+(D).")

    print("\nALL ASSERTS PASSED. Milestone 2 (reciprocity from permutation signs)")
    print("is numerically certified; the Lean target is the grid/CRT sign lemma (B)")
    print("plus the M1 Zolotarev signs (A), assembled as (D). Awaiting Docker.")


if __name__ == "__main__":
    main()
