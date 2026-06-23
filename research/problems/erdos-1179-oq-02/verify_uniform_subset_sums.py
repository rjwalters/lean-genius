#!/usr/bin/env python3
"""
Build-free ORIENT experiment for erdos-1179-oq-02.

Erdős Problem #1179 (PROVED for the main asymptotic): for 0<ε<1 let g_ε(N) be
the minimal k such that a uniformly random k-subset A of an abelian group G of
size N has, w.h.p. as N→∞, an ε-uniform subset-sum representation function
    F_A(g) = #{S ⊆ A : Σ_{x∈S} x = g},   |F_A(g) − 2^k/N| ≤ ε·2^k/N  ∀g.
Known: g_ε(N) ≥ log₂N (trivial); Erdős–Rényi (1965) g_ε ≤ (2+o(1))log₂N;
Erdős–Hall (1976) g_ε ≤ (1 + O_ε(log log log N / log log N))·log₂N.

oq-02 (this OQ): can the (1+o(1)) FACTOR be sharpened to an additive constant,
    g_ε(N) ≤ log₂N + O_ε(1)  ?
This is OPEN and analytic — this script does NOT resolve it. It gives an honest,
reproducible small-N computation that (a) grounds the Lean definitions in the
parent file (the identity Σ_g F_A(g) = 2^|A|), (b) confirms the trivial lower
bound g_ε(N) ≥ ⌈log₂N⌉ empirically, and (c) tabulates the EXACT empirical
additive gap  g_ε(N) − log₂N  for the cyclic group G = ℤ/N over small N, as
data informing whether the gap looks bounded.

We use G = ℤ/N (one canonical abelian group; the OQ is over all abelian G —
documented caveat). "w.h.p." is rendered finitely as: the EXACT fraction of
k-subsets A ⊆ G that are ε-uniform, and g_ε^p(N) := least k with that fraction
≥ p (we report p ∈ {1.0, 0.9}).
"""
import math
from itertools import combinations


def repr_counts(A, N):
    """F_A(g) for all g in Z/N, via all 2^|A| subset sums. Returns list length N."""
    F = [0] * N
    # iterate subsets of A by bitmask
    k = len(A)
    for mask in range(1 << k):
        s = 0
        m = mask
        idx = 0
        while m:
            if m & 1:
                s += A[idx]
            m >>= 1
            idx += 1
        F[s % N] += 1
    return F


def is_eps_uniform(F, k, N, eps):
    exp = (2.0 ** k) / N
    tol = eps * exp
    return all(abs(f - exp) <= tol + 1e-12 for f in F)


def check_total_identity(N_max=10):
    """Sanity: Σ_g F_A(g) = 2^|A| for every subset (grounds the parent Lean defs)."""
    bad = []
    for N in range(2, N_max + 1):
        elems = list(range(N))
        for k in range(0, N + 1):
            for A in combinations(elems, k):
                F = repr_counts(list(A), N)
                if sum(F) != (1 << k):
                    bad.append((N, A))
                    break
    assert not bad, f"identity Σ_g F_A(g)=2^|A| FAILED at {bad[:5]}"
    print(f"[ID] OK  Σ_g F_A(g) = 2^|A| for every subset of Z/N, N≤{N_max}")


def g_eps(N, eps, p):
    """Least k such that fraction of ε-uniform k-subsets of Z/N is ≥ p.
    Returns (k, fraction_at_k). p=1.0 means ALL k-subsets uniform."""
    elems = list(range(N))
    for k in range(0, N + 1):
        subsets = list(combinations(elems, k))
        if not subsets:
            continue
        good = sum(1 for A in subsets if is_eps_uniform(repr_counts(list(A), N), k, N, eps))
        frac = good / len(subsets)
        if frac >= p - 1e-12:
            return k, frac
    return None, 0.0


def main():
    check_total_identity(N_max=9)

    print("\n[LB] Trivial lower bound g_ε(N) ≥ ⌈log₂N⌉ (no k<log₂N is ε-uniform):")
    eps_lb = 0.5
    for N in range(2, 13):
        elems = list(range(N))
        kmax_below = math.floor(math.log2(N) - 1e-9)  # largest k with 2^k < N
        any_uniform_below = False
        for k in range(0, kmax_below + 1):
            if any(is_eps_uniform(repr_counts(list(A), N), k, N, eps_lb)
                   for A in combinations(elems, k)):
                any_uniform_below = True
                break
        flag = "OK" if not any_uniform_below else "VIOLATED"
        print(f"   N={N:2d}  log₂N={math.log2(N):5.2f}  ⌈log₂N⌉={math.ceil(math.log2(N)):d}  "
              f"no ε-uniform k<log₂N: {flag}")

    print("\n[GAP] Empirical additive gap g_ε(N) − log₂N on G=ℤ/N (p = required fraction):")
    for eps in (0.5, 0.9):
        print(f"  ε={eps}:")
        print(f"    {'N':>3} {'log2N':>6} | {'g(p=1.0)':>9} {'gap':>6} | {'g(p=0.9)':>9} {'gap':>6}")
        for N in range(2, 13):
            l2 = math.log2(N)
            k1, f1 = g_eps(N, eps, 1.0)
            k9, f9 = g_eps(N, eps, 0.9)
            gap1 = (k1 - l2) if k1 is not None else float('nan')
            gap9 = (k9 - l2) if k9 is not None else float('nan')
            s1 = f"{k1}" if k1 is not None else "—"
            s9 = f"{k9}" if k9 is not None else "—"
            print(f"    {N:>3} {l2:>6.2f} | {s1:>9} {gap1:>6.2f} | {s9:>9} {gap9:>6.2f}")

    print("\nNotes:")
    print(" - Data is for the single group ℤ/N; the OQ ranges over all abelian G")
    print("   (an elementary-abelian 2-group can behave differently — caveat).")
    print(" - p=1.0 (every k-subset uniform) is a conservative finite proxy for")
    print("   'w.h.p.'; p=0.9 is closer to the probabilistic statement.")
    print(" - This computation cannot decide the asymptotic O_ε(1) question; it only")
    print("   exhibits the exact small-N gap and confirms the structural bounds.")
    print("\nALL CHECKS PASSED")


if __name__ == "__main__":
    main()
