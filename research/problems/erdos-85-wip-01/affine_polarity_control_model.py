#!/usr/bin/env python3
"""Design-level control model for NONBIP-CONNECTED / A-REG (outline v2.29).

The (q^2_q) configuration "AG(2,q) minus one parallel class" with the polarity

    point (a,b)  <->  line { y = a x - b }

has symmetric incidence d = a c - b, so its incidence matrix A is a symmetric
0/1 q-regular C4-free matrix on q^2 vertices.  It satisfies every hypothesis of
A-REG (BinarySquareRegularExclusion) EXCEPT two, and it fails both in the most
instructive way:

  (i)  tr A = q: exactly q absolute points (2b = a^2; for q even the column a=0),
       where A-REG needs tr A = 0 (a fixed-point-free polarity);
  (ii) the deficiency graph D = (q-1)I + J - A^2 is the dropped parallel class,
       D = q * K_q, DISCONNECTED, with mult_D(-1) = q^2 - q.

So the classical object sits one property away from a counterexample, at the
union-of-cliques extreme of the -1 multiplicity.  The theorem A-REG needs is a
Baer-type absolute-point theorem for self-polar (q^2_q) configurations whose
non-collinearity graph is connected.

This script checks (i) and (ii) exactly for prime q (prime-field arithmetic;
the prime-power case needs GF(q) arithmetic but the identities are the same).
"""
from __future__ import annotations

import argparse
import sys


def build(q: int):
    pts = [(a, b) for a in range(q) for b in range(q)]
    idx = {p: i for i, p in enumerate(pts)}
    n = q * q
    A = [[0] * n for _ in range(n)]
    for (a, b) in pts:
        for (c, d) in pts:
            if (d - (a * c - b)) % q == 0:
                A[idx[(a, b)]][idx[(c, d)]] = 1
    return pts, A


def check(q: int) -> bool:
    pts, A = build(q)
    n = len(pts)
    sym = all(A[i][j] == A[j][i] for i in range(n) for j in range(n))
    tr = sum(A[i][i] for i in range(n))
    deg = {sum(r) for r in A}
    common = [[sum(A[i][k] * A[j][k] for k in range(n)) for j in range(n)]
              for i in range(n)]
    c4free = all(common[i][j] <= 1 for i in range(n) for j in range(n) if i != j)
    D = [[1 if i != j and common[i][j] == 0 else 0 for j in range(n)]
         for i in range(n)]
    ddeg = {sum(r) for r in D}
    # components of D
    seen, comps, sizes = set(), 0, []
    for s in range(n):
        if s in seen:
            continue
        comps += 1
        stack, size = [s], 0
        while stack:
            u = stack.pop()
            if u in seen:
                continue
            seen.add(u)
            size += 1
            stack += [v for v in range(n) if D[u][v]]
        sizes.append(size)
    # each D-component is a clique iff D = q*K_q
    clique = all(
        all(D[i][j] for i in range(n) for j in range(n)
            if i != j and comp[i] == comp[j])
        for comp in [None]) if False else None
    print(f"q={q} n={n} symmetric={sym} C4free={c4free} deg={deg} "
          f"trA(absolute points)={tr} Ddeg={ddeg} Dcomponents={comps} "
          f"sizes={sorted(set(sizes))}")
    ok = sym and c4free and deg == {q} and tr == q and ddeg == {q - 1} \
        and comps == q and set(sizes) == {q}
    return ok


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--q", type=int, nargs="*", default=[3, 5, 7])
    args = ap.parse_args()
    allok = True
    for q in args.q:
        allok &= check(q)
    print(f"affine_polarity_control_verified={allok}")
    sys.exit(0 if allok else 1)
