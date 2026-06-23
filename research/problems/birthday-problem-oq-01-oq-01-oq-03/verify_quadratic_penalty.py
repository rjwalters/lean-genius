#!/usr/bin/env python3
"""
birthday-problem-oq-01-oq-01-oq-03  (researcher-1) — QUANTITATIVE non-uniformity
penalty for the no-collision probability.

Prior sessions settled the SIGNS (qualitative extrema):
  * E[X] = C(n,2)·Σpₖ²  is MINIMIZED by uniform (Cauchy–Schwarz)  [PR #23219]
  * Pr(X=0) = n!·eₙ(p)   is MAXIMIZED by uniform (Schur-concavity) [PR #24449]
where eₙ is the n-th elementary symmetric polynomial and the n birthdays are
i.i.d. with day-probabilities p = (p₁,…,p_d), Σpₖ = 1.

This session adds the missing QUANTITATIVE leading penalty, tying both extrema
to ONE non-uniformity scalar, the L² defect
        V(p) := Σₖ (pₖ − 1/d)²  =  Σpₖ² − 1/d        (the SOS identity).

Two exact statements, certified below to high precision against exact eₙ:

(1)  EXACT, all n:   E[X] − E_uniform[X]  =  C(n,2)·V(p).
     (immediate from E[X]=C(n,2)Σpₖ² and the SOS identity; V = relative excess /d).

(2)  SECOND ORDER:   write pₖ = 1/d + δₖ, Σδₖ = 0, V = Σδₖ². Expanding eₙ:
        eₙ(p) = d^{-n}[ C(d,n) − ½ d² C(d-2,n-2) V ] + O(δ³),
     the first-order term vanishes (uniform is critical), and therefore the
     no-collision-probability deficit is

        Pr_u(X=0) − Pr_p(X=0)  =  Kd_{n,d} · V(p) + O(V^{3/2}),
        Kd_{n,d} = ½ · n! · d^{2-n} · C(d-2, n-2)   ( ≥ 0 ).

     So a hash function with L² bias V has a no-collision-probability penalty
     proportional to V, with explicit coefficient Kd — the cryptographically
     relevant leading-order law, sharper than the sign-only Schur result.
     For n=2 it is EXACT (K = 1): Pr(X=0) = 1 − Σpₖ², deficit = V exactly.

Derivation of (2): ∏_{k∈S}(1/d+δₖ) = d^{-n}∏(1+dδₖ)
   = d^{-n}[1 + d Σ_{k∈S}δₖ + d² Σ_{i<j∈S}δᵢδⱼ + …]. Summing over all n-subsets S:
   Σ_S Σ_{k∈S}δₖ = C(d-1,n-1)Σδ = 0;
   Σ_S Σ_{i<j∈S}δᵢδⱼ = C(d-2,n-2)Σ_{i<j}δᵢδⱼ = C(d-2,n-2)·½((Σδ)²−Σδ²) = −½C(d-2,n-2)V.

Docker-independent.  Exact arithmetic via fractions + mpmath for the O(V^{3/2}) fit.
"""
from fractions import Fraction as Fr
from itertools import combinations
from math import comb, factorial
import mpmath as mp

mp.mp.dps = 40


def esymm(p, n):
    """Exact n-th elementary symmetric polynomial of the list p."""
    return sum((prod_fr(p[i] for i in S) for S in combinations(range(len(p)), n)), Fr(0))


def prod_fr(it):
    out = Fr(1)
    for x in it:
        out *= x
    return out


def V(p):
    d = len(p)
    return sum((pk - Fr(1, d)) ** 2 for pk in p)


def check_exact_EX(d, n, trials=400):
    """(1) E[X]-E_u[X] = C(n,2)·V exactly, over random rational distributions."""
    import random
    bad = 0
    for _ in range(trials):
        raw = [Fr(random.randint(1, 50)) for _ in range(d)]
        s = sum(raw)
        p = [x / s for x in raw]
        EX = Fr(comb(n, 2)) * sum(pk * pk for pk in p)
        EXu = Fr(comb(n, 2)) * Fr(1, d)
        if EX - EXu != Fr(comb(n, 2)) * V(p):
            bad += 1
    return bad


def K(n, d):
    return Fr(factorial(n)) * Fr(comb(d - 2, n - 2)) * Fr(1, 2) / Fr(d) ** (n - 2)


def check_quadratic(d, n):
    """(2) Pr_u(X=0)-Pr_p(X=0) = K·V + O(V^{3/2}); verify K via V->0 scaling."""
    import random
    # a fixed mean-zero direction delta, then scale by t -> 0
    delta = [Fr(random.randint(-9, 9)) for _ in range(d - 1)]
    delta.append(-sum(delta))            # enforce Σδ = 0
    # pick a base scale so 1/d + t*δ stays a valid distribution for small t
    Vdir = sum(x * x for x in delta)     # V at t=1 (unscaled direction)
    ratios = []
    prn = factorial(n)
    eu = esymm([Fr(1, d)] * d, n)
    Pru = Fr(prn) * eu
    for t in [mp.mpf("1e-3"), mp.mpf("1e-4"), mp.mpf("1e-5")]:
        # build p = 1/d + t*delta with mpmath (t small, exact eₙ via mpmath floats)
        pp = [mp.mpf(1) / d + t * mp.mpf(int(x.numerator)) / mp.mpf(int(x.denominator))
              for x in delta]  # delta are ints here so denominator=1
        # exact-ish eₙ over mpmath
        en = mp.mpf(0)
        for S in combinations(range(d), n):
            term = mp.mpf(1)
            for i in S:
                term *= pp[i]
            en += term
        Prp = prn * en
        Vt = sum((pp[i] - mp.mpf(1) / d) ** 2 for i in range(d))
        Pru_mp = mp.mpf(str(Pru.numerator)) / mp.mpf(str(Pru.denominator))
        deficit = Pru_mp - Prp
        ratios.append(deficit / Vt)  # -> K as t->0
    Kpred = K(n, d)
    Kpred_f = mp.mpf(str(Kpred.numerator)) / mp.mpf(str(Kpred.denominator))
    return ratios, Kpred_f


if __name__ == "__main__":
    print("birthday-oq-01-oq-01-oq-03 :: quantitative non-uniformity penalty")
    print("=" * 70)
    print("\n(1) EXACT  E[X]-E_u[X] = C(n,2)*V(p)  over random rational distributions")
    allok = True
    for d in range(2, 9):
        for n in range(2, d + 1):
            bad = check_exact_EX(d, n, trials=200)
            allok &= (bad == 0)
            if bad:
                print(f"   d={d} n={n}: {bad} MISMATCHES")
    print(f"   -> {'all exact (0 mismatches)' if allok else 'FAILURES above'}")

    print("\n(2) Pr_u(X=0)-Pr_p(X=0) = K*V + O(V^{3/2}); deficit/V -> K as V->0")
    print(f"   {'(n,d)':>8} | {'K predicted':>18} | {'deficit/V at t=1e-3,1e-4,1e-5':>40}")
    print("   " + "-" * 76)
    ok2 = True
    for (n, d) in [(2, 3), (2, 5), (3, 5), (3, 6), (4, 6), (2, 8), (5, 8)]:
        ratios, Kp = check_quadratic(d, n)
        conv = ", ".join(mp.nstr(r, 8) for r in ratios)
        # convergence: ratio at 1e-5 should match K to ~4-5 digits
        err = abs(ratios[-1] - Kp)
        ok2 &= (err < mp.mpf("1e-3") * (abs(Kp) + 1))
        print(f"   {str((n,d)):>8} | {mp.nstr(Kp,12):>18} | {conv}")
    print("   " + "-" * 76)
    print(f"   -> {'deficit/V converges to predicted K (coefficient certified)' if ok2 else 'CONVERGENCE FAILED'}")

    print("\n" + "=" * 70)
    print("RESULT:", "PASS" if (allok and ok2) else "FAIL")
    print("Both extrema are governed by the single L2 non-uniformity V=Σ(pₖ-1/d)²:")
    print("  E[X] excess = C(n,2)·V (exact);  Pr(X=0) deficit = K·V + O(V^{3/2}),")
    print("  K = ½·n!·d^{2-n}·C(d-2,n-2).  This is the crypto-relevant leading law.")
