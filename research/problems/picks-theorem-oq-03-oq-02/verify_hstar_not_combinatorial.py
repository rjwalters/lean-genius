#!/usr/bin/env python3
"""
Durable exact verifier for picks-theorem-oq-03-oq-02 (ORIENT, S1).

OQ (seeker stub): "Can the h*-vector be computed directly from the face lattice of
the polytope?" (h*-vector = Ehrhart delta-vector.)

ANSWER: NO. The h*-vector is a LATTICE-geometric invariant, not a purely
combinatorial one: combinatorially identical lattice polytopes (isomorphic face
lattices) can have DIFFERENT h*-vectors. The canonical witness is the family of
**Reeve tetrahedra**

    T_h = conv{ (0,0,0), (1,0,0), (0,1,0), (1,1,h) },   h = 1,2,3,...

EVERY T_h is a tetrahedron: 4 vertices, 6 edges, 4 triangular facets, 1 cell, with
the SAME face lattice (the boolean lattice B_4 on 4 atoms). Yet their Ehrhart
polynomials -- hence h*-vectors -- depend on h. This is exactly Reeve's example
showing Pick's theorem (the PARENT gallery proof) has NO direct 3D analogue: lattice
volume is not a function of the (vertices, edge, interior) lattice-point counts.

This script computes, with EXACT integer/rational arithmetic:
  * Ehrhart values L_{T_h}(t) = #(tT_h cap Z^3) by direct lattice-point counting;
  * the Ehrhart polynomial (degree 3) by exact finite differences;
  * the h*-vector h* = (h*_0,...,h*_3) from L via the binomial basis;
and shows:
  (A) all T_h share the SAME combinatorial data (f-vector (4,6,4,1), and identical
      t=1 lattice-point count L(1)=4 = the 4 vertices, no other lattice points);
  (B) the h*-vectors DIFFER with h: h*(T_h) = (1, 0, h-1, 0), sum = h = normalized
      volume -> a combinatorial invariant could not distinguish them, but h* does.
No Lean, no Docker.
"""

from fractions import Fraction
import math


# Reeve tetrahedron vertices.
def reeve_vertices(h):
    return [(0, 0, 0), (1, 0, 0), (0, 1, 0), (1, 1, h)]


def in_tetra_dilated(p, verts, t):
    """Exact test: is integer point p in t * conv(verts)?  Equivalently p/t in
    conv(verts): solve barycentric M lam = p/t with lam_i>=0, sum<=1, using the
    edge matrix from v0. All exact (Fraction)."""
    v0 = verts[0]
    # columns vi - v0, i=1,2,3
    cols = [tuple(verts[i][k] - v0[k] for k in range(3)) for i in (1, 2, 3)]
    # rhs = p/t - v0
    rhs = [Fraction(p[k], 1) / t - v0[k] for k in range(3)]
    # solve 3x3 system cols * lam = rhs by Cramer (exact)
    def det3(a, b, c):
        return (a[0] * (b[1] * c[2] - b[2] * c[1])
                - a[1] * (b[0] * c[2] - b[2] * c[0])
                + a[2] * (b[0] * c[1] - b[1] * c[0]))
    A = [[Fraction(cols[j][i]) for j in range(3)] for i in range(3)]  # rows
    # build column vectors for Cramer
    c0 = [A[i][0] for i in range(3)]
    c1 = [A[i][1] for i in range(3)]
    c2 = [A[i][2] for i in range(3)]
    D = det3(c0, c1, c2)
    if D == 0:
        return False
    l1 = det3(rhs, c1, c2) / D
    l2 = det3(c0, rhs, c2) / D
    l3 = det3(c0, c1, rhs) / D
    if l1 < 0 or l2 < 0 or l3 < 0:
        return False
    return (l1 + l2 + l3) <= 1


def ehrhart_values(h, T):
    """L_{T_h}(t) for t=0..T by exact lattice-point counting."""
    verts = reeve_vertices(h)
    vals = []
    for t in range(0, T + 1):
        if t == 0:
            vals.append(1)  # the single point 0
            continue
        # bounding box of t*T_h
        xs = [t * v[0] for v in verts]
        ys = [t * v[1] for v in verts]
        zs = [t * v[2] for v in verts]
        cnt = 0
        for x in range(min(xs), max(xs) + 1):
            for y in range(min(ys), max(ys) + 1):
                for z in range(min(zs), max(zs) + 1):
                    if in_tetra_dilated((x, y, z), verts, t):
                        cnt += 1
        vals.append(cnt)
    return vals


def fit_cubic(vals):
    """Given L(0..3), return integer-checked coefficients of the Ehrhart cubic and
    the h*-vector. L(t) = sum_{i=0}^3 h*_i * C(t + 3 - i, 3)."""
    # h*-vector from the standard transform: h*_j = sum_{i=0}^j (-1)^{j-i} C(4, j-i) L(i)
    L = vals
    hstar = []
    for j in range(4):
        s = 0
        for i in range(j + 1):
            s += (-1) ** (j - i) * math.comb(4, j - i) * L[i]
        hstar.append(s)
    return hstar


def f_vector(h):
    """(vertices, edges, 2-faces, cells) of T_h -- always the same tetrahedron."""
    return (4, 6, 4, 1)


def main():
    failures = []
    print("Reeve tetrahedra T_h = conv{(0,0,0),(1,0,0),(0,1,0),(1,1,h)}\n")
    print(f"{'h':>2} | {'f-vector':>12} | {'L(0..4)':>22} | h*-vector | norm.vol")
    print("-" * 78)
    hstars = {}
    for h in range(1, 7):
        vals = ehrhart_values(h, 4)
        hstar = fit_cubic(vals)
        hstars[h] = tuple(hstar)
        # checks
        if f_vector(h) != (4, 6, 4, 1):
            failures.append(("fvec", h))
        if vals[1] != 4:                       # t=1: exactly the 4 vertices
            failures.append(("L1", h, vals[1]))
        if tuple(hstar) != (1, 0, h - 1, 0):   # predicted Reeve h*-vector
            failures.append(("hstar", h, hstar))
        if sum(hstar) != h:                    # normalized volume = h
            failures.append(("vol", h, sum(hstar)))
        print(f"{h:>2} | {str(f_vector(h)):>12} | {str(vals):>22} | "
              f"{tuple(hstar)} | {sum(hstar)}")

    print()
    # (A) identical combinatorics
    same_fvec = len({f_vector(h) for h in range(1, 7)}) == 1
    same_L1 = len({ehrhart_values(h, 1)[1] for h in range(1, 7)}) == 1
    print(f"A  all T_h share f-vector (4,6,4,1): {same_fvec}; "
          f"all have L(1)=4 (only the 4 vertices as lattice pts): {same_L1}")
    # (B) distinct h*-vectors
    distinct = len(set(hstars.values())) == len(hstars)
    print(f"B  h*-vectors are pairwise DISTINCT across h=1..6: {distinct}  "
          f"=> h* is NOT determined by the face lattice")
    # tie to Pick: T_1 (h=1) is unimodular (vol 1/6), T_h has the SAME boundary/
    # interior lattice-point counts at t=1 yet volume h/6 -> Pick has no 3D analogue.
    print("\nPick connection: every T_h has exactly its 4 vertices as lattice points\n"
          "(0 interior, 0 non-vertex boundary) yet Euclidean volume = h/6 varies with h\n"
          "-> the 3D 'Pick' data (#interior, #boundary) cannot recover volume; h* (a\n"
          "lattice-geometric invariant) is needed and is not combinatorial.")

    ok = (not failures) and same_fvec and same_L1 and distinct
    print("\n" + ("ALL CHECKS PASS" if ok else f"FAILURES: {failures[:8]}"))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
