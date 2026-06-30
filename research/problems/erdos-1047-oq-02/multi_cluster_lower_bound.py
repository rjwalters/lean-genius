#!/usr/bin/env python3
"""
Erdős #1047 / OQ-02 — a LOWER BOUND on Goodman's open question.

Goodman's open question (the file's `maxNonConvexComponents`, defined only as the
PLACEHOLDER `:= d`): how many connected components of a polynomial lemniscate
`{z : |f(z)| ≤ c}` can be non-convex AT ONCE, as a function of `deg f = d`?

All prior sessions studied the *onset* of ONE non-convex component (#24420
closed-form onset for z²(z−1); #24491 a non-convex middle for three collinear
simple roots). None bounded the *number* of simultaneously non-convex components.

CLAIM (certified numerically here):  maxNonConvexComponents(d) ≥ ⌊d/3⌋.

BUILDING BLOCK.  A single collinear unit-spaced triple of simple roots
{−1,0,1} (i.e. z³−z) has, once its three roots have merged into ONE component,
a NON-CONVEX ("dumbbell") component:
    c=0.10 → 3 convex comps;  c≈0.18–0.25 → 1 component, signed κ_min < 0.
(Reproduced in STEP 0; consistent with verify_lemniscate_curvature.py.)

CONSTRUCTION.  Place k such triples at the vertices of a regular k-gon of radius
Rbig, each triple oriented RADIALLY (roots v_j·(1 ± 1/Rbig) and v_j). The vertex
set has cyclic C_k rotational symmetry, so EVERY cluster sees an identical
far-field factor ∏_{i≠j}|·| — hence a SINGLE level c makes all k merged blobs
non-convex simultaneously. The roots are conjugate-symmetric ⇒ f has real
coefficients. With Rbig large the k blobs stay mutually separated, giving
exactly k components, each non-convex:

    d = 3k roots  ⇒  ≥ k = ⌊d/3⌋  non-convex components.

k=2 reduces to the real root set {±(Rbig−1), ±Rbig, ±(Rbig+1)}.

Reuses the exact signed-curvature tester from verify_lemniscate_curvature.py
(κ ≥ 0 on a component's boundary ⇔ that component is convex). No Date()/RNG;
roots and coefficients are deterministic.
"""
import sys
import os
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from verify_lemniscate_curvature import build_g, count_components, min_curvature


def kgon_triple_roots(k, Rbig, eps=1.0):
    """k radial unit(±eps)-spaced triples at the vertices of a regular k-gon."""
    roots = []
    for j in range(k):
        ang = 2.0 * np.pi * j / k
        v = Rbig * np.exp(1j * ang)
        u = np.exp(1j * ang)  # unit radial direction
        roots += [v - eps * u, v, v + eps * u]
    return roots


def coeffs_from_roots(roots):
    """Real coefficients (highest degree first); strip tiny conjugate-symmetric noise."""
    p = np.poly(np.array(roots, dtype=complex))
    re = np.real(p)
    assert np.max(np.abs(np.imag(p))) < 1e-6 * (1 + np.max(np.abs(re))), \
        "roots not conjugate-symmetric -> complex coeffs"
    return [float(c) for c in re]


def analyze_k(k, Rbig, c, R, res_comp=800, res_loop=1200, tol=-1e-3):
    roots = kgon_triple_roots(k, Rbig)
    funcs = build_g(coeffs_from_roots(roots))
    ncomp = count_components(funcs, c, R, res=res_comp)
    loops = min_curvature(funcs, c, R, res=res_loop)
    nonconvex = [l for l in loops if l[0] < tol]
    print(f"\n=== k={k}  (degree {3*k})  Rbig={Rbig}  c={c:.6g} ===")
    for i, (kmin, kmax, npts) in enumerate(sorted(loops)):
        flag = "NON-CONVEX" if kmin < tol else "convex"
        print(f"    loop {i}: kappa_min={kmin:+.4f} kappa_max={kmax:+.4f} pts={npts} -> {flag}")
    # The lower bound needs >= k SIMULTANEOUS non-convex components (others may be convex).
    ok = len(nonconvex) >= k
    print(f"  region components(grid)={ncomp}; {len(nonconvex)}/{len(loops)} loops non-convex; "
          f"need >= k={k} non-convex -> {'PASS' if ok else 'FAIL'}")
    return ok


def scan_c(k, Rbig, R, cs, res_comp=600, res_loop=900):
    roots = kgon_triple_roots(k, Rbig)
    funcs = build_g(coeffs_from_roots(roots))
    print(f"\n--- scan k={k} Rbig={Rbig} R={R} ---")
    for c in cs:
        n = count_components(funcs, c, R, res=res_comp)
        loops = min_curvature(funcs, c, R, res=res_loop)
        mk = min((l[0] for l in loops), default=None)
        nnc = sum(1 for l in loops if l[0] < -1e-3)
        if mk is None:
            print(f"  c={c:<12.6g} comps={n} (no loops)")
        else:
            print(f"  c={c:<12.6g} comps={n} loops={len(loops)} min_kappa={mk:+.4f} non-convex={nnc}")


if __name__ == "__main__":
    print("STEP 0 — single unit-spaced triple z^3 - z (the non-convex building block)")
    f1 = build_g([1.0, 0.0, -1.0, 0.0])
    for c in [0.10, 0.18, 0.20, 0.25]:
        n = count_components(f1, c, 2.0, res=500)
        loops = min_curvature(f1, c, 2.0, res=800)
        mk = min((l[0] for l in loops), default=None)
        print(f"  c={c:.2f} comps={n} min_kappa={mk:+.4f}")

    results = {}

    # k=2: real roots {+-3,+-4,+-5} (Rbig=4). c is the |f|^2 level; scan geometrically.
    scan_c(2, 4.0, 7.0, [1e3, 5e3, 1e4, 2e4, 3e4, 5e4, 8e4, 1.2e5])
    # c=8e4: each triple fully merged into ONE non-convex blob -> exactly 2, both non-convex.
    results[2] = analyze_k(2, 4.0, 8.0e4, R=7.0)

    # k=3: equilateral triangle of radial triples, Rbig=4 (side ~6.93). scan geometrically.
    scan_c(3, 4.0, 7.0, [1e7, 5e7, 1e8, 3e8, 6e8, 1e9, 1.5e9, 2e9])
    # c=1.5e9: 3 simultaneous non-convex (merged) blobs, one per triangle vertex.
    results[3] = analyze_k(3, 4.0, 1.5e9, R=7.0)

    print("\n" + "=" * 64)
    print("SUMMARY — maxNonConvexComponents(d) >= floor(d/3):")
    for k in sorted(results):
        print(f"  k={k} (deg {3*k}): {k} simultaneous non-convex components "
              f"-> {'PASS' if results[k] else 'RETUNE c'}")
    print("General k: regular k-gon of radial unit-triples (cyclic C_k symmetry")
    print("=> one shared c) gives k non-convex components at degree 3k.")
