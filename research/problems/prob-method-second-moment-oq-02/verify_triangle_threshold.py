#!/usr/bin/env python3
r"""
prob-method-second-moment-oq-02 — triangle subgraph threshold in G(n, p).

The slug's application layer culminates in the canonical second-moment result:
the threshold for a triangle in the Erdős–Rényi random graph G(n, p) is
p*(n) = 1/n, with
  * subcritical  n·p → 0  ⟹  Pr(triangle) → 0   (first moment / Markov), and
  * supercritical n·p → ∞  ⟹  Pr(triangle) → 1   (second moment / Paley–Zygmund).

The genuinely case-heavy step (flagged in the tracker as the "Paley–Zygmund
overlap-class calculation", the part with deferred Lean sorries) is the SECOND
MOMENT of the triangle count X = number of triangles in G(n,p). This script
certifies that calculation EXACTLY — symbolically in p and cross-checked against
brute-force enumeration — so the eventual Lean §C has a verified target.

----------------------------------------------------------------------------
The overlap-class second moment (the heart of the matter)
----------------------------------------------------------------------------
Write X = Σ_T 1[T ⊆ G] over the C(n,3) triangle slots T. Two distinct triangle
slots T, T' can share |V∩| ∈ {0,1,2} vertices; only |V∩|=2 forces a shared edge.
Classify ordered pairs (T,T') by the size |E(T) ∪ E(T')| of their joint edge set:

  | overlap            | #ordered pairs              | |E∪E'| |
  |--------------------|-----------------------------|--------|
  | T' = T  (3 verts)  | C(n,3)                      |   3    |
  | 2 shared vertices  | C(n,3)·3·(n−3)              |   5    |
  | 1 shared vertex    | C(n,3)·3·C(n−3,2)           |   6    |
  | 0 shared vertices  | C(n,3)·C(n−3,3)             |   6    |

E[X²] = Σ_{T,T'} p^{|E∪E'|}, and Var[X] = E[X²] − E[X]² with E[X] = C(n,3)·p³.
The dominant variance term is the shared-EDGE class (exponent 5):

  Var[X] = C(n,3)·p³ + 3·C(n,3)·(n−3)·p⁵ − C(n,3)·(3n−8)·p⁶.

Var[X]/E[X]² → 0 (so Paley–Zygmund forces X>0 whp) iff n·p → ∞; at the critical
window p = c/n it tends to 6/c³ (Poisson(c³/6) regime). This pins p* = 1/n.

Exact (sympy + Fraction); brute force enumerates all 2^C(n,2) graphs for small n.
Run:  python3 verify_triangle_threshold.py     (exit 0 ⇔ all pass)
"""

from __future__ import annotations
import itertools
from math import comb, isqrt  # noqa: F401

import sys

try:
    import sympy as sp
except Exception:
    print("sympy required"); sys.exit(2)

p, n, c = sp.symbols("p n c", positive=True)

# ---------------------------------------------------------------------------
# Closed forms via overlap classes
# ---------------------------------------------------------------------------

def EX_closed(N):
    return sp.binomial(N, 3) * p**3

def EX2_closed(N):
    C = sp.binomial(N, 3)
    return (C * 1 * p**3
            + C * 3 * (N - 3) * p**5
            + C * 3 * sp.binomial(N - 3, 2) * p**6
            + C * sp.binomial(N - 3, 3) * p**6)

def Var_closed(N):
    return sp.expand(EX2_closed(N) - EX_closed(N)**2)

def Var_compact(N):
    """The hand-derived compact form, to be checked equal to Var_closed."""
    C = sp.binomial(N, 3)
    return sp.expand(C * p**3 + 3 * C * (N - 3) * p**5 - C * (3 * N - 8) * p**6)

# ---------------------------------------------------------------------------
# Brute force: enumerate all graphs on N labelled vertices, weighted by p
# ---------------------------------------------------------------------------

def brute_moments(N):
    verts = list(range(N))
    edges = list(itertools.combinations(verts, 2))
    tris = list(itertools.combinations(verts, 3))
    tri_edges = [tuple(itertools.combinations(t, 2)) for t in tris]
    m = len(edges)
    eidx = {e: i for i, e in enumerate(edges)}
    EX = sp.Integer(0)
    EX2 = sp.Integer(0)
    for mask in range(1 << m):
        present = [(mask >> eidx[e]) & 1 for e in edges]
        k = sum(present)                       # number of edges in this graph
        w = p**k * (1 - p)**(m - k)            # probability weight
        # count triangles present
        x = 0
        for te in tri_edges:
            if all(present[eidx[e]] for e in te):
                x += 1
        EX += w * x
        EX2 += w * x * x
    return sp.expand(EX), sp.expand(EX2)

# ---------------------------------------------------------------------------
# Checks
# ---------------------------------------------------------------------------

def check_overlap_counts(N):
    """The four overlap-class ordered-pair counts sum to C(N,3)²."""
    C = sp.binomial(N, 3)
    total = C * (1 + 3 * (N - 3) + 3 * sp.binomial(N - 3, 2) + sp.binomial(N - 3, 3))
    return sp.simplify(total - C**2) == 0

def main():
    print("=" * 74)
    print("prob-method-second-moment-oq-02 — triangle threshold p* = 1/n in G(n,p)")
    print("=" * 74)
    ok = True

    # (1) overlap-class counts are exhaustive
    cnt_ok = all(check_overlap_counts(N) for N in range(3, 12))
    ok &= cnt_ok
    print(f"(1) overlap-class ordered-pair counts sum to C(n,3)²  (n=3..11): "
          f"{'OK' if cnt_ok else 'FAIL'}")

    # (2) compact Var equals the raw overlap-class Var (symbolic in N)
    var_id = sp.simplify(Var_closed(n) - Var_compact(n)) == 0
    ok &= var_id
    print(f"(2) Var compact form == overlap-class Var (symbolic in n): "
          f"{'OK' if var_id else 'FAIL'}")
    print(f"    Var[X] = C(n,3)·[ p³ + 3(n-3)p⁵ - (3n-8)p⁶ ]")

    # (3) brute force vs closed forms, exact in p, for small n
    print("(3) brute-force enumeration vs closed forms (exact in p):")
    bf_ok = True
    for N in (3, 4, 5, 6):
        EXb, EX2b = brute_moments(N)
        EXc, EX2c = sp.expand(EX_closed(N)), sp.expand(EX2_closed(N))
        e_ok = sp.simplify(EXb - EXc) == 0
        e2_ok = sp.simplify(EX2b - EX2c) == 0
        bf_ok &= (e_ok and e2_ok)
        print(f"    n={N}: E[X] {'OK' if e_ok else 'FAIL'},  E[X²] {'OK' if e2_ok else 'FAIL'}"
              f"   (2^{comb(N,2)} graphs)")
    ok &= bf_ok

    # (4) threshold behaviour at p = c/n, n → ∞
    print("(4) threshold at p = c/n  (n → ∞):")
    EXsub = EX_closed(n).subs(p, c / n)
    limEX = sp.limit(sp.expand(EXsub), n, sp.oo)        # depends on c
    # E[X] at p=c/n → c³/6 (a finite constant: subcritical c→0 ⟹ 0; first moment)
    EX_lim_ok = sp.simplify(limEX - c**3 / 6) == 0
    print(f"    E[X]|_(p=c/n) → c³/6   : {'OK' if EX_lim_ok else 'FAIL'}  "
          f"(→0 as c→0  ⟹  subcritical Markov: Pr(triangle)→0)")
    ratio = sp.simplify(Var_closed(n).subs(p, c / n) / (EX_closed(n).subs(p, c / n))**2)
    limratio = sp.limit(ratio, n, sp.oo)
    ratio_ok = sp.simplify(limratio - 6 / c**3) == 0
    print(f"    Var[X]/E[X]²|_(p=c/n) → 6/c³ : {'OK' if ratio_ok else 'FAIL'}  "
          f"(→0 as c→∞  ⟹  supercritical Paley–Zygmund: Pr(triangle)→1)")
    ok &= (EX_lim_ok and ratio_ok)

    print("-" * 74)
    print(f"threshold p*(n) = 1/n confirmed: E[X]=C(n,3)p³ collapses for np→0,")
    print(f"Var/E²→0 for np→∞. Both moment certificates exact + brute-verified.")
    print("-" * 74)
    print("ALL PASS" if ok else "SOME CHECKS FAILED")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
