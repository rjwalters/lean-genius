#!/usr/bin/env python3
"""Certificate for the residue-3 (mod 4) Dirichlet-witness obstruction.

The registered flagship `proofs/Proofs/ThreeSquares.lean` routes the ENTIRE
sufficiency direction of Legendre's three-square theorem through the single
axiom `dirichlet_key_lemma`, whose hypothesis is the witness

    exists d > 0, p = d*m - 1 prime, legendreSym p (-d) = 1.

`Proofs.ThreeSquaresSufficiency` isolates the open content as
`DirichletWitnessProperty`: a witness exists for EVERY non-excluded m with
4 doesnt-divide m and m > 1.

This script certifies (build-free) the theorem proved in
`proofs/Proofs/ThreeSquaresWitnessObstruction.lean`:

  THEOREM.  If m == 3 (mod 4), p != 2 is prime, p = d*m - 1, d > 0, then
            legendreSym p (-d) = -1.

  COROLLARY.  DirichletWitnessProperty is FALSE (witness: m = 11).

Two independent confirmations:

  [A] Brute force: over all m == 3 (mod 4) and all valid (d, p) up to bounds,
      legendreSym p (-d) is ALWAYS -1 (never 1).  Upgrades the earlier numerical
      result (m == 3 mod 8, 0/750 -- audit PR #24529) to the full m == 3 mod 4
      class.

  [B] Step-by-step reciprocity identity, matching the Lean proof exactly:
        (-d/p) = (-1/p) * (d/p)                    [multiplicativity]
        (d/p)  = (m/p)            since d*m = p+1 ≡ 1 (mod p)
        (m/p)  = (-1)^{(m/2)(p/2)} * (p/m)         [Jacobi reciprocity]
        (p/m)  = (-1/m) = -1      since p ≡ -1 (mod m), m ≡ 3 (mod 4)
        (-1)^{(m/2)(p/2)} = (-1)^{p/2} = (-1/p)    since m/2 is odd
      ==> (-d/p) = (-1/p) * (m/p) = (-1/p) * (-(-1/p)) = -1.
      Each intermediate Jacobi/Legendre symbol is recomputed and checked.

  [C] Contrast: for the residues the witness CAN serve (m % 4 in {1, 2},
      i.e. m % 8 in {1, 2, 5, 6}), a witness with value +1 is found, so the
      obstruction is specific to m % 4 == 3.
"""

from sympy import isprime, jacobi_symbol


def legendre_neg_d(d, p):
    """legendreSym p (-d) for p an odd prime (Jacobi == Legendre here)."""
    return jacobi_symbol((-d) % p, p)


def check_A(m_bound=6000, d_bound=400):
    bad = 0
    tot = 0
    for m in range(3, m_bound):
        if m % 4 != 3:
            continue
        for d in range(1, d_bound):
            p = d * m - 1
            if p > 2 and isprime(p):
                tot += 1
                if legendre_neg_d(d, p) != -1:
                    bad += 1
                    if bad <= 5:
                        print(f"  COUNTEREXAMPLE m={m} d={d} p={p}")
    print(f"[A] m%4==3: legendreSym p(-d) == -1 for all valid (d,p): "
          f"counterexamples={bad}/{tot}")
    return bad == 0


def check_B(m_bound=2000, d_bound=120):
    """Verify each step of the reciprocity identity used by the Lean proof."""
    mism = 0
    tot = 0
    for m in range(3, m_bound):
        if m % 4 != 3:
            continue
        for d in range(1, d_bound):
            p = d * m - 1
            if not (p > 2 and isprime(p)):
                continue
            tot += 1
            # primitive symbols
            sym_neg_d = jacobi_symbol((-d) % p, p)        # (-d/p)
            sym_neg1_p = jacobi_symbol((-1) % p, p)        # (-1/p)
            sym_d_p = jacobi_symbol(d % p, p)              # (d/p)
            sym_m_p = jacobi_symbol(m % p, p)              # (m/p)
            sym_p_m = jacobi_symbol(p % m, m)              # (p/m)
            sym_neg1_m = jacobi_symbol((-1) % m, m)        # (-1/m)
            # step 1: (-d/p) = (-1/p)*(d/p)
            s1 = (sym_neg_d == sym_neg1_p * sym_d_p)
            # step 2: (d/p) = (m/p)   [d*m = p+1 ≡ 1 mod p]
            s2 = (d * m) % p == 1 and (sym_d_p == sym_m_p)
            # step 3: reciprocity (m/p) = (-1)^{(m//2)(p//2)} (p/m)
            sign = (-1) ** ((m // 2) * (p // 2))
            s3 = (sym_m_p == sign * sym_p_m)
            # step 4: (p/m) = (-1/m) = -1
            s4 = (p % m == (m - 1)) and (sym_p_m == sym_neg1_m) and (sym_neg1_m == -1)
            # step 5: sign = (-1)^{p//2} = (-1/p)   [m//2 odd]
            s5 = ((m // 2) % 2 == 1) and (sign == (-1) ** (p // 2)) \
                and ((-1) ** (p // 2) == sym_neg1_p)
            # conclusion
            s6 = (sym_neg_d == -1)
            if not (s1 and s2 and s3 and s4 and s5 and s6):
                mism += 1
                if mism <= 5:
                    print(f"  STEP MISMATCH m={m} d={d} p={p}: "
                          f"{s1=} {s2=} {s3=} {s4=} {s5=} {s6=}")
    print(f"[B] reciprocity-identity steps verified: mismatches={mism}/{tot}")
    return mism == 0


def check_C():
    samples = [1, 2, 5, 6, 9, 10, 13, 14, 17, 18, 21, 22]  # m%4 in {1,2}
    ok = 0
    for m in samples:
        found = False
        for d in range(1, 800):
            p = d * m - 1
            if p > 2 and isprime(p) and legendre_neg_d(d, p) == 1:
                found = True
                break
        ok += found
    print(f"[C] m%4 in {{1,2}}: witness with value +1 found for {ok}/{len(samples)} samples")
    return ok == len(samples)


def check_falsity_witness():
    """m = 11 is the concrete falsifier used in `not_dirichletWitnessProperty`."""
    m = 11
    # non-excluded: 11 = 3^2 + 1^2 + 1^2
    assert 3 ** 2 + 1 ** 2 + 1 ** 2 == m
    assert m % 4 != 0
    # no witness with value +1
    found = any(
        (p := d * m - 1) > 2 and isprime(p) and legendre_neg_d(d, p) == 1
        for d in range(1, 5000)
    )
    print(f"[D] m=11 falsifier: non-excluded sum-of-3-squares, 4-free, "
          f"witness-with-value-+1 exists = {found}")
    return not found


if __name__ == "__main__":
    a = check_A()
    b = check_B()
    c = check_C()
    d = check_falsity_witness()
    print()
    print("ALL CHECKS PASS" if (a and b and c and d) else "FAILURE")
